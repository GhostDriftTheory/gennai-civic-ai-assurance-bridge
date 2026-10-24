#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""自治体AI・プライバシーアシュアランス PoC第2弾。
Copyright © 2026 AI Assurance, Inc. All rights reserved. See README.md.

python poc.py                   : 全46ケース・7シナリオを実行し、ローカル結果を保存
python poc.py demo cumulative   : 累積開示のシナリオを実行
python poc.py test              : 自己テスト（外部依存なし）
python poc.py verify output     : 保存記録と模擬受信・採用ファイルを再検証
python poc.py ci                : Python/JavaScript照合＋Leanモデルと具体命題の検査

公開用の固定・有限ルール参照実装。外部通信・実AI・実住民データなし。
送信先役はローカルファイル。全システムの通信遮断を提供する製品ではない。
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import html
import itertools
import json
import re
import shutil
import subprocess
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
REFERENCE_SHA256 = '7ad18cd83dc87acbca7ca0895d64e74b68b1c7e4df461e0800c8e301571aeda7'
STATUSES = ('PASS', 'HOLD', 'REJECT')
MAX_BYTES = 4 * 1024 * 1024
STATE_KEYS = {'scope', 'known', 'pending', 'disclosed', 'used_ids', 'revision'}
REQUEST_KEYS = {'request_id','source_id','purpose','use','human_confirmation','role','basis','basis_id',
                'recipient','terms','terms_version','region','training','retention_days','fields',
                'transform','evidence','payload_patch','response','outcome'}
RESPONSE_MODES = {'safe','leak_name','extra_field','missing_binding','wrong_binding','unsafe_use','changed_text'}

class InputError(ValueError):
    """入力形式エラー。業務判定のPASS/HOLD/REJECTと区別する。"""

def require(ok: bool, message: str) -> None:
    if not ok:
        raise InputError(message)

def canonical(x: Any) -> str:
    return json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(',', ':'), allow_nan=False)

def digest(x: Any) -> str:
    return hashlib.sha256(canonical(x).encode('utf-8')).hexdigest()

def tree(x: Any, depth: int = 0) -> None:
    require(depth <= 24, 'JSONの入れ子が深すぎます。')
    if x is None or type(x) is bool:
        return
    if type(x) is int:
        require(0 <= x <= 1000000, '数値は0〜1,000,000の整数に限定します。')
    elif type(x) is str:
        require(len(x) <= 20000 and not any(0xD800 <= ord(c) <= 0xDFFF for c in x), '文字列が不正です。')
    elif type(x) is list:
        require(len(x) <= 5000, '配列が大きすぎます。')
        for v in x:
            tree(v, depth + 1)
    elif type(x) is dict:
        require(len(x) <= 100 and all(type(k) is str and k.isascii() for k in x), 'JSONキーはASCII文字列です。')
        for k, v in x.items():
            tree(k, depth + 1); tree(v, depth + 1)
    else:
        raise InputError('未対応の型です（浮動小数点は使用しません）。')

def parse_json(text: str) -> Any:
    def pairs(xs):
        r = {}
        for k, v in xs:
            require(k not in r, 'JSONキーの重複：' + k)
            r[k] = v
        return r
    def bad(v):
        raise InputError('NaN/Infinityは使用できません。')
    try:
        r = json.loads(text.lstrip('\ufeff'), object_pairs_hook=pairs, parse_constant=bad)
        tree(r)
        return r
    except (json.JSONDecodeError, RecursionError) as e:
        raise InputError('JSONを解釈できません。') from e

def read_json(path: Path) -> Any:
    require(path.is_file() and path.stat().st_size <= MAX_BYTES, 'ファイルがないか、4MBを超えています：' + str(path))
    return parse_json(path.read_text(encoding='utf-8-sig'))

def keys(x: Any, allowed: set[str], name: str) -> None:
    require(type(x) is dict and set(x) == allowed, name + 'の項目が欠落または過剰です。')

def nonempty(x: Any) -> bool:
    return type(x) is str and 0 < len(x) <= 200

def worst(xs: list[str]) -> str:
    require(all(x in STATUSES for x in xs), '判定値が不正です。')
    return 'REJECT' if 'REJECT' in xs else 'HOLD' if 'HOLD' in xs else 'PASS'

def checked(ok: bool) -> str:
    return 'PASS' if ok else 'REJECT'

def supported(known: bool, ok: bool) -> str:
    return checked(ok) if known else 'HOLD'

def write_json(path: Path, x: Any) -> None:
    path.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def envelope(r: dict, data: dict) -> dict:
    return {'request_id':r['request_id'], 'recipient':r['recipient'], 'purpose':r['purpose'], 'use':r['use'],
            'region':r['region'], 'training':r['training'], 'retention_days':r['retention_days'],
            'terms_version':r['terms_version'], 'data':copy.deepcopy(data)}

def render_text(data: dict) -> str:
    parts = ['【架空の案内文案】相談分野：' + data['topic'] + '。']
    if data['age_band']:
        parts.append('年代：' + data['age_band'] + '。')
    if data['household_band']:
        parts.append('世帯人数：' + data['household_band'] + '。')
    parts.append('子育て相談窓口の公開情報と、相談時の確認事項を職員が確認してください。')
    parts.append('これは制度の受給・資格を決定するものではありません。')
    return ''.join(parts)

class Engine:
    def __init__(self, data: dict):
        tree(data)
        keys(data, {'schema','metadata','policy','sources','base_request','tests','scenarios'}, 'cases.json')
        require(data['schema'] == 'civic-privacy-cases/1.0', '未対応のケース形式です。')
        require(digest({'policy':data['policy'],'sources':data['sources']}) == REFERENCE_SHA256,
                '固定したデモ仕様・合成資料が一致しません。仕様変更にはコードと証明のレビューが必要です。')
        self.data = copy.deepcopy(data)
        self.policy = self.data['policy']; self.sources = self.data['sources']
        self.tests = {t['key']:t for t in self.data['tests']}
        require(len(self.tests) == len(self.data['tests']) and len(self.tests) >= 30, 'テスト定義が重複または不足しています。')
        for t in self.tests.values():
            keys(t, {'key','label','changes','seed','expected_send','expected_adopt'}, 'test')
            require(t['expected_send'] in STATUSES and t['expected_adopt'] in STATUSES, '期待値が不正です。')
        self.validate_request(self.data['base_request'])

    def state(self, seed: dict | None = None) -> dict:
        seed = seed or {}
        require(type(seed) is dict and set(seed) <= STATE_KEYS, '台帳初期値が不正です。')
        s = {'scope':'SYN-A','known':True,'pending':False,'disclosed':[],'used_ids':[],'revision':0}
        s.update(copy.deepcopy(seed))
        s['disclosed'] = sorted(s['disclosed'])
        self.validate_state(s)
        return s

    def validate_state(self, s: dict) -> None:
        tree(s); keys(s, STATE_KEYS, 'state')
        require(s['scope'] in self.sources, '台帳の対象範囲が不正です。')
        require(type(s['known']) is bool and type(s['pending']) is bool, '台帳確認フラグの型が不正です。')
        require(type(s['revision']) is int and 0 <= s['revision'] <= 10000, '台帳の版が不正です。')
        for k in ['disclosed','used_ids']:
            require(type(s[k]) is list and len(s[k]) <= 1000 and all(nonempty(v) for v in s[k]), '台帳の配列が不正です。')
            require(len(s[k]) == len(set(s[k])), '台帳の要素が重複しています。')
        require(s['disclosed'] == sorted(s['disclosed']) and set(s['disclosed']) <= set(self.policy['fields']), '未定義・未整列の開示項目です。')

    def validate_request(self, r: dict) -> None:
        tree(r); keys(r, REQUEST_KEYS, 'request')
        for k in REQUEST_KEYS - {'human_confirmation','training','retention_days','fields','evidence','payload_patch','basis_id'}:
            require(nonempty(r[k]), k + 'は空でない文字列です。')
        require(r['basis_id'] is None or nonempty(r['basis_id']), '利用根拠参照の型が不正です。')
        for k in ['human_confirmation','training','evidence']:
            require(type(r[k]) is bool, k + 'は真偽値です。')
        require(type(r['retention_days']) is int and 0 <= r['retention_days'] <= 3650, '保持日数の型・範囲が不正です。')
        require(type(r['fields']) is list and len(r['fields']) <= 20 and all(nonempty(v) for v in r['fields']), '項目一覧の型が不正です。')
        require(len(r['fields']) == len(set(r['fields'])), '項目一覧が重複しています。')
        require(type(r['payload_patch']) is dict and len(r['payload_patch']) <= 20, '最終内容の差分が不正です。')
        for k, v in r['payload_patch'].items():
            require(nonempty(k) and type(v) is str and len(v) <= 500, '最終内容の差分は短い文字列に限定します。')
        require(r['basis'] in {'confirmed','missing','denied'} and r['terms'] in {'confirmed','missing'}, '検査資料の区分が不正です。')
        require(r['response'] in RESPONSE_MODES and r['outcome'] in {'ack','unknown'}, '模擬応答の区分が不正です。')

    def request(self, changes: dict | None = None, request_id: str | None = None) -> dict:
        changes = changes or {}
        require(type(changes) is dict and set(changes) <= REQUEST_KEYS, '未定義の変更項目です。')
        r = copy.deepcopy(self.data['base_request']); r.update(copy.deepcopy(changes))
        if request_id is not None and 'request_id' not in changes:
            r['request_id'] = request_id
        self.validate_request(r)
        return r

    def prepare(self, r: dict) -> tuple[dict, dict]:
        """固定の合成資料から項目単位で変換。自然文の匿名化処理ではない。"""
        src = self.sources.get(r['source_id'])
        if src is None:
            prepared = {}
        else:
            values = dict(src)
            values.update(age_band=f"{src['age']//10*10}代",
                          household_band='2人以下' if src['household_size'] <= 2 else '3人以上')
            prepared = {k:values.get(k,'[未定義項目]') for k in r['fields']}
        wire = copy.deepcopy(prepared); wire.update(copy.deepcopy(r['payload_patch']))
        return prepared, wire

    def units(self, fields: list | set) -> int:
        return sum(self.policy['fields'][k]['units'] for k in set(fields))

    def observations(self, r: dict, s: dict) -> dict:
        """元入力・固定資料・台帳から原子的比較を抽出。判定値を入力にしない。"""
        self.validate_request(r); self.validate_state(s)
        p = self.policy; prepared, wire = self.prepare(r)
        new = set(wire) & set(p['fields']) - set(s['disclosed'])
        known_basis = r['basis'] != 'missing' and r['basis_id'] is not None
        return {'sourceOK':r['source_id'] in self.sources and r['source_id'] == s['scope'],
            'scopeOK':r['purpose'] == p['purpose'] and r['use'] == p['use'] and r['human_confirmation'],
            'authorityKnown':known_basis,
            'authorityOK':r['basis'] == 'confirmed' and r['basis_id'] == p['basis_id'] and r['role'] == p['role'],
            'termsKnown':r['terms'] == 'confirmed',
            'recipientOK':r['recipient'] == p['recipient'],
            'termsOK':r['terms_version'] == p['terms_version'] and r['region'] == p['region'] and not r['training'] and r['retention_days'] == 0,
            'fieldsOK':bool(wire) and set(wire) <= set(p['fields']),
            'evidenceKnown':r['evidence'],
            'payloadOK':r['transform'] == p['transform'] and canonical(wire) == canonical(prepared),
            'ledgerKnown':s['known'], 'pending':s['pending'], 'duplicate':r['request_id'] in s['used_ids'],
            'used':self.units(s['disclosed']), 'additional':self.units(new), 'limit':p['budget_limit']}

    def evaluate(self, r: dict, s: dict) -> dict:
        o = self.observations(r, s)
        statuses = [checked(o['sourceOK']), checked(o['scopeOK']),
            supported(o['authorityKnown'],o['authorityOK']),
            worst([checked(o['recipientOK']),supported(o['termsKnown'],o['termsOK'])]),
            checked(o['fieldsOK']),supported(o['evidenceKnown'],o['payloadOK']),
            supported(o['ledgerKnown'],o['used'] + o['additional'] <= o['limit']),
            'REJECT' if o['duplicate'] else 'HOLD' if o['pending'] else 'PASS']
        details = [
            '登録された合成資料と、このセッションの対象が一致。' if o['sourceOK'] else '未登録の資料、または台帳と異なる対象です。',
            '子育て相談・職員確認用の下書きに限定。' if o['scopeOK'] else '目的・用途または人間の確認条件が範囲外です。',
            'デモ用の利用根拠参照・職員区分を確認。' if statuses[2]=='PASS' else '利用根拠の参照が未確認です。' if statuses[2]=='HOLD' else '利用根拠の内容・参照または権限が一致しません。',
            '許可済みの模擬送信先・取扱条件と一致。' if statuses[3]=='PASS' else '送信先の取扱条件が未確認です。' if statuses[3]=='HOLD' else '送信先・版・地域・学習利用・保持日数のいずれかが条件外です。',
            '最終送信内容は公開デモで許可した項目だけ。' if o['fieldsOK'] else '氏名・詳細住所・自由文等の許可外項目、または空の要求です。',
            '固定の変換結果と、実際に模擬送信する内容を照合。' if statuses[5]=='PASS' else '変換の対応を確認する検査資料がありません。' if statuses[5]=='HOLD' else '変換方式または最終送信内容が対応しません。',
            f"既開示 {o['used']} ＋ 新規 {o['additional']} ＝ {o['used']+o['additional']} / 上限 {o['limit']}（デモ点数）。" if o['ledgerKnown'] else '累積開示の履歴を確認できません。',
            '未確定の送信・要求IDの重複はありません。' if statuses[7]=='PASS' else '前回の結果が未確定のため、後続処理を保留。' if statuses[7]=='HOLD' else '実行済みの要求IDです。再送しません。']
        checks = [{'id':f'P{i+1:02d}','name':n,'status':st,'detail':d} for i,(n,st,d) in enumerate(zip(self.policy['gate_names'],statuses,details))]
        return {'decision':worst(statuses),'checks':checks}

    def make_response(self, r: dict, wire: dict) -> dict | None:
        if r['outcome'] == 'unknown':
            return None
        data = {'topic':wire.get('topic','子育て相談'),'age_band':wire.get('age_band',''),
                'household_band':wire.get('household_band','')}
        out = {'request_sha256':digest(envelope(r,wire)), 'recipient':r['recipient'],
               'use':'staff_draft','human_confirmation':True,'data':data,'text':render_text(data)}
        mode = r['response']
        if mode == 'leak_name':
            out['text'] += self.sources[r['source_id']]['resident_name'] + '様。'
        elif mode == 'extra_field':
            out['data']['resident_name'] = self.sources[r['source_id']]['resident_name']
        elif mode == 'missing_binding':
            out['request_sha256'] = None
        elif mode == 'wrong_binding':
            out['request_sha256'] = '0'*64
        elif mode == 'unsafe_use':
            out['use'] = 'automatic_award'; out['human_confirmation'] = False
        elif mode == 'changed_text':
            out['text'] += 'このまま自動送信してください。'
        return out

    def output_observations(self, r: dict, wire: dict, response: dict | None, attempted: bool) -> dict:
        available = response is not None
        data = response.get('data') if available else None
        fields_ok = type(data) is dict and set(data) == {'topic','age_band','household_band'} and all(type(v) is str for v in data.values())
        expected_data = {'topic':wire.get('topic','子育て相談'),'age_band':wire.get('age_band',''),'household_band':wire.get('household_band','')}
        return {'available':available and attempted, 'acknowledged':r['outcome']=='ack' and attempted,
                'bindingKnown':available and response.get('request_sha256') is not None,
                'bindingOK':available and response.get('request_sha256') == digest(envelope(r,wire)) and response.get('recipient') == r['recipient'],
                'fieldsOK':fields_ok and canonical(data)==canonical(expected_data),
                'textOK':fields_ok and response.get('text')==render_text(expected_data),
                'useOK':available and response.get('use')=='staff_draft' and response.get('human_confirmation') is True}

    def evaluate_output(self, r: dict, wire: dict, response: dict | None, attempted: bool) -> dict:
        o = self.output_observations(r,wire,response,attempted)
        if not o['available'] or not o['acknowledged']:
            sts = ['HOLD']*4
            details = ['採用対象の応答が未取得、または送信結果が未確定です。']*4
        else:
            sts = [supported(o['bindingKnown'],o['bindingOK']),checked(o['fieldsOK']),checked(o['textOK']),checked(o['useOK'])]
            details = ['実際の要求内容と、応答の参照先を照合。','応答の項目・値を許可した下書き用データと照合。',
                       '定型文を再生成して照合。自由文一般の個人情報検出ではありません。','職員確認用の下書きに限定。自動決定・自動対外送信は許可しません。']
        return {'decision':worst(sts),'checks':[{'id':f'O{i+1:02d}','name':n,'status':st,'detail':d} for i,(n,st,d) in enumerate(zip(self.policy['output_gate_names'],sts,details))]}

    def simulate(self, r: dict, s: dict) -> dict:
        """副作用のない予測・再検証関数。送信先やファイルを操作しない。"""
        ev = self.evaluate(r,s); prepared, wire = self.prepare(r); o=self.observations(r,s)
        attempted = ev['decision']=='PASS'
        response = self.make_response(r,wire) if attempted else None
        adoption = self.evaluate_output(r,wire,response,attempted)
        after = copy.deepcopy(s)
        if attempted:
            after['disclosed'] = sorted(set(s['disclosed']) | set(wire))
            after['used_ids'].append(r['request_id']); after['revision'] += 1
            after['pending'] = r['outcome']=='unknown'
        return {'prepared':prepared,'wire':wire,'request_sha256':digest(envelope(r,wire)),
            'send':ev,'attempted':attempted,'acknowledged':attempted and r['outcome']=='ack',
            'response':response,'adoption':adoption,'after':after,
            'new_fields':sorted((set(wire) & set(self.policy['fields']))-set(s['disclosed'])),
            'units_before':o['used'],'units_proposed':o['used']+o['additional'],
            'units_after':self.units(after['disclosed'])}

    def packet(self, r: dict, before: dict, result: dict) -> dict:
        payload = {'schema':'civic-privacy-record/1.0','demo_only':True,'reference_sha256':REFERENCE_SHA256,
                   'as_of':self.policy['as_of'],'request':copy.deepcopy(r),'before':copy.deepcopy(before),'result':copy.deepcopy(result)}
        h=digest(payload)
        return {'record_id':'P2-'+h[:16].upper(),'payload':payload,'sha256':h}

    def verify(self, record: dict, expected_before: dict | None = None) -> dict:
        tree(record); keys(record,{'record_id','payload','sha256'},'record')
        p=record['payload']; keys(p,{'schema','demo_only','reference_sha256','as_of','request','before','result'},'payload')
        require(p['schema']=='civic-privacy-record/1.0' and p['demo_only'] is True,'デモ用記録ではありません。')
        result=self.simulate(p['request'],p['before'])
        h=digest(p)
        intact=record['sha256']==h and record['record_id']=='P2-'+h[:16].upper()
        spec=p['reference_sha256']==REFERENCE_SHA256 and p['as_of']==self.policy['as_of']
        replay=canonical(result)==canonical(p['result'])
        history=expected_before is None or canonical(expected_before)==canonical(p['before'])
        return {'ok':intact and spec and replay and history,'intact':intact,'specification':spec,'replayed':replay,'history':history,
                'send':result['send']['decision'],'adoption':result['adoption']['decision']}

    def scenario(self, key: str) -> dict:
        for s in self.data['scenarios']:
            if s['key']==key:
                return s
        raise InputError('シナリオがありません：'+key)

    def scenario_requests(self, key: str):
        s=self.scenario(key)
        for i, step in enumerate(s['steps']):
            t=self.tests[step['test']]
            changes={**t['changes'],**step.get('changes',{})}
            r=self.request(changes,f'{key.upper()}-{i+1:02d}')
            yield r,step.get('expected_send',t['expected_send']),step.get('expected_adopt',t['expected_adopt'])

class LocalMockReceiver:
    """許可された要求をローカルの受信ファイルへ書く。ネットワークAPIは持たない。"""
    def __init__(self, engine: Engine, folder: Path | None = None):
        self.engine=engine; self.folder=folder; self.received=[]
        if folder is not None:
            folder.mkdir(parents=True,exist_ok=True)

    def receive(self, request: dict, encoded: bytes) -> dict | None:
        parsed=parse_json(encoded.decode('utf-8'))
        self.received.append(encoded)
        if self.folder is not None:
            # ファイル名を要求入力から組み立てない。
            with (self.folder/f'{len(self.received):04d}.json').open('xb') as f:
                f.write(encoded)
        return self.engine.make_response(request,parsed['data'])

class Session:
    def __init__(self, engine: Engine, seed: dict | None = None, receiver: LocalMockReceiver | None = None):
        self.engine=engine; self.state=engine.state(seed)
        self.receiver=receiver or LocalMockReceiver(engine)
        self.records=[]; self.drafts=[]

    def execute(self, r: dict) -> dict:
        before=copy.deepcopy(self.state)
        result=self.engine.simulate(r,before)
        # この分岐が実際のローカル送信境界。非PASSでは受信先を呼び出さない。
        if result['send']['decision']=='PASS':
            encoded=canonical(envelope(r,result['wire'])).encode('utf-8')
            # 確認不能の例外でも履歴を返却しない（本版ではセッションを保守的に凍結）。
            self.state=copy.deepcopy(result['after']); self.state['pending']=True
            actual=self.receiver.receive(r,encoded)
            require(canonical(actual)==canonical(result['response']),'模擬応答が予測と一致しません。状態は未確定で保持します。')
            self.state=copy.deepcopy(result['after'])
        record=self.engine.packet(r,before,result)
        require(self.engine.verify(record,before)['ok'],'記録の生成・再検証が成立しません。')
        self.records.append(record)
        if result['adoption']['decision']=='PASS':
            self.drafts.append(result['response']['text'])
        return record


def self_tests(engine: Engine) -> list[dict]:
    rows=[]
    def check(name, fn):
        try:
            ok=fn() is True
            rows.append({'name':name,'passed':ok,'detail':'OK' if ok else '期待不一致'})
        except Exception as e:
            rows.append({'name':name,'passed':False,'detail':f'{type(e).__name__}: {e}'})
    def blocked(fn):
        try:
            fn()
        except (InputError, ValueError, TypeError):
            return True
        return False
    for t in engine.tests.values():
        s=Session(engine,t['seed']); r=engine.request(t['changes'],'TEST-'+t['key'])
        p=s.execute(r); result=p['payload']['result']
        check(t['key']+' / 期待判定',lambda t=t,x=result:x['send']['decision']==t['expected_send'] and x['adoption']['decision']==t['expected_adopt'])
        check(t['key']+' / 実送信境界',lambda s=s,x=result:len(s.receiver.received)==int(x['send']['decision']=='PASS') and (not s.receiver.received or s.receiver.received[0]==canonical(envelope(s.records[0]['payload']['request'],x['wire'])).encode()))
        check(t['key']+' / 記録再検証',lambda p=p:engine.verify(p)['ok'])
        check(t['key']+' / 出力採用',lambda s=s,x=result:len(s.drafts)==int(x['adoption']['decision']=='PASS'))
    for scenario in engine.data['scenarios']:
        def verify_sequence(k=scenario['key']):
            s=Session(engine); previous=engine.state()
            for r,es,ea in engine.scenario_requests(k):
                p=s.execute(r); x=p['payload']['result']
                if x['send']['decision']!=es or x['adoption']['decision']!=ea or not engine.verify(p,previous)['ok']:
                    return False
                previous=x['after']
            return canonical(s.state)==canonical(previous)
        check('連続シナリオ / '+scenario['key'],verify_sequence)
    base=engine.request(); state=engine.state(); original=engine.packet(base,state,engine.simulate(base,state))
    mutations={'request_id':None,'human_confirmation':'true','training':0,'retention_days':True,'fields':'topic',
               'basis':'unknown-value','response':'arbitrary','outcome':'success','payload_patch':[], 'evidence':1}
    for k,v in mutations.items():
        check('不正入力 / '+k,lambda k=k,v=v:blocked(lambda:engine.request({k:v})))
    for name,ch in [('重複項目',{'fields':['topic','topic']}),('負の日数',{'retention_days':-1}),
                    ('未知項目',{'unknown':True}),('Unicode',{'purpose':'\ud800'})]:
        check('不正入力 / '+name,lambda c=ch:blocked(lambda:engine.request(c)))
    for text in ['{"a":1,"a":2}','{"x":NaN}','{"x":Infinity}','{"x":0.5}','{"x":-1}','{"x":"\\ud800"}']:
        check('JSON拒否 / '+repr(text),lambda text=text:blocked(lambda:parse_json(text)))
    for ch in [{'known':1},{'pending':'false'},{'disclosed':['resident_name']},{'disclosed':['area','area']},
               {'used_ids':['X','X']},{'revision':False},{'scope':'OTHER'}]:
        check('台帳型検査 / '+repr(ch),lambda c=ch:blocked(lambda:engine.state(c)))
    paths=[('result.send.decision','REJECT'),('result.adoption.decision','REJECT'),('result.attempted',False),
           ('result.acknowledged',False),('result.after.disclosed',[]),('result.after.pending',True),
           ('result.after.used_ids',[]),('result.units_after',0),('result.wire.age_band','50代'),
           ('result.response.text','書換え'),('reference_sha256','0'*64),('as_of','2020-01-01')]
    for path,val in paths:
        def tamper(path=path,val=val):
            p=copy.deepcopy(original); x=p['payload']; bits=path.split('.')
            for k in bits[:-1]: x=x[k]
            x[bits[-1]]=val
            h=digest(p['payload']); p['sha256']=h;p['record_id']='P2-'+h[:16].upper()
            return not engine.verify(p)['ok']
        check('記録改変＋再ハッシュ / '+path,tamper)
    check('独立履歴との照合',lambda:not engine.verify(original,engine.state({'disclosed':['age_band']}))['ok'])
    def unknown_keeps_budget():
        s=Session(engine); a=s.execute(engine.request({'outcome':'unknown'},'UNKNOWN-1')); used=engine.units(s.state['disclosed'])
        b=s.execute(engine.request(request_id='UNKNOWN-2'))
        return used==2 and s.state['pending'] and len(s.receiver.received)==1 and b['payload']['result']['send']['decision']=='HOLD' and engine.units(s.state['disclosed'])==used
    check('結果不明の消費保持と後続停止',unknown_keeps_budget)
    def receiver_throws():
        class Broken(LocalMockReceiver):
            def receive(self,request,encoded):
                self.received.append(encoded); raise OSError('simulated receiver failure')
        s=Session(engine,receiver=Broken(engine))
        try: s.execute(base)
        except OSError: pass
        return s.state['pending'] and engine.units(s.state['disclosed'])==2 and len(s.drafts)==0
    check('送信先例外でも未確定・消費保持',receiver_throws)
    for sts in [('REJECT','HOLD'),('PASS','HOLD'),(),('PASS',)*8]:
        check('集約 / '+repr(sts),lambda sts=sts:worst(list(sts))==('REJECT' if 'REJECT' in sts else 'HOLD' if 'HOLD' in sts else 'PASS'))
    check('期待ラベルは判定入力にしない',lambda:engine.evaluate(base,state)['decision']=='PASS')
    check('送信失敗でも元入力を変更しない',lambda:canonical(base)==canonical(engine.data['base_request']) and canonical(state)==canonical(engine.state()))
    return rows


def verify_folder(engine: Engine, folder: Path) -> int:
    index_path=folder/'index.json'
    index=read_json(index_path)
    keys(index,{'schema','groups'},'index')
    require(index['schema']=='civic-privacy-run/1.0' and type(index['groups']) is list and 0<len(index['groups'])<=200,'実行索引が不正です。')
    directories=[]
    for group in index['groups']:
        keys(group,{'directory','seed','records'},'index.group')
        require(type(group['directory']) is str and re.fullmatch(r'[A-Za-z0-9_-]+',group['directory']) is not None,'グループ名が不正です。')
        require(type(group['records']) is list and 0<len(group['records'])<=100,'記録一覧が不正です。')
        directories.append(group['directory'])
    require(len(directories)==len(set(directories)),'グループが重複しています。')
    require(set(directories)=={p.name for p in folder.iterdir() if p.is_dir()},'実行索引に含まれないグループがあります。')
    total=0
    for group in index['groups']:
        prior=engine.state(group['seed']); receipts=0; drafts=0
        location=folder/group['directory']
        require(location.resolve().is_relative_to(folder.resolve()),'保存先の範囲が不正です。')
        require(group['records']==sorted(p.name for p in (location/'records').iterdir()),'記録一覧が保存ファイルと一致しません。')
        for name in group['records']:
            require(re.fullmatch(r'\d{4}\.json',name) is not None,'記録ファイル名が不正です。')
            packet=read_json(location/'records'/name); require(engine.verify(packet,prior)['ok'],'記録の連続再検証に失敗しました。')
            result=packet['payload']['result']; prior=result['after']; total+=1
            if result['attempted']:
                receipts+=1; wire=location/'outbox'/f'{receipts:04d}.json'
                require(wire.is_file() and wire.read_bytes()==canonical(envelope(packet['payload']['request'],result['wire'])).encode('utf8'),'模擬受信内容が一致しません。')
            if result['adoption']['decision']=='PASS':
                drafts+=1; path=location/'drafts'/f'{drafts:04d}.txt'
                require(path.is_file() and path.read_text(encoding='utf8')==result['response']['text'],'採用文案が一致しません。')
        require(len(list((location/'outbox').iterdir()))==receipts and len(list((location/'drafts').iterdir()))==drafts,'未認定の追加ファイルがあります。')
    return total


def run(engine: Engine, out_root: Path, scenario_key: str | None = None) -> Path:
    if scenario_key is not None: engine.scenario(scenario_key)
    root=out_root/('run-'+uuid.uuid4().hex[:10]); root.mkdir(parents=True,exist_ok=False)
    groups=[]; summary_rows=[]
    if scenario_key is None:
        for i,t in enumerate(engine.tests.values()):
            groups.append((f'test-{i+1:02d}',t['label'],t['seed'],[(engine.request(t['changes'],'TEST-'+t['key']),t['expected_send'],t['expected_adopt'])]))
    for scenario in engine.data['scenarios']:
        if scenario_key is None or scenario['key']==scenario_key:
            groups.append(('scenario-'+scenario['key'],scenario['title'],{},list(engine.scenario_requests(scenario['key']))))
    index={'schema':'civic-privacy-run/1.0','groups':[]}
    for directory,label,seed,requests in groups:
        folder=root/directory;(folder/'records').mkdir(parents=True);(folder/'drafts').mkdir()
        session=Session(engine,seed,LocalMockReceiver(engine,folder/'outbox'))
        record_names=[]
        for j,(r,es,ea) in enumerate(requests):
            packet=session.execute(r); result=packet['payload']['result']
            require(result['send']['decision']==es and result['adoption']['decision']==ea,'期待判定不一致：'+label)
            name=f'{j+1:04d}.json';write_json(folder/'records'/name,packet);record_names.append(name)
            if result['adoption']['decision']=='PASS':
                (folder/'drafts'/f'{len(session.drafts):04d}.txt').write_text(session.drafts[-1],encoding='utf8')
            summary_rows.append({'label':label,'step':j+1,'send':result['send']['decision'],'adopt':result['adoption']['decision'],
                                 'attempted':result['attempted'],'units':result['units_after'],'record':directory+'/records/'+name})
        index['groups'].append({'directory':directory,'seed':engine.state(seed),'records':record_names})
    write_json(root/'index.json',index)
    tested=self_tests(engine);require(all(t['passed'] for t in tested),'自己テストが失敗しました。')
    write_json(root/'self_test_report.json',{'total':len(tested),'passed':sum(t['passed'] for t in tested),'results':tested})
    count=verify_folder(engine,root)
    report={'ok':True,'records_verified':count,'self_tests':len(tested),'rows':summary_rows,
            'scope':'Synthetic local reference implementation; no real network, AI, legal certification or general anonymisation.'}
    write_json(root/'summary.json',report)
    (root/'report.html').write_text(report_html(report),encoding='utf8')
    print(f"保存記録とファイルの再検証：{count}/{count}\n自己テスト：{len(tested)}/{len(tested)}\n結果：{root/'report.html'}")
    return root


def report_html(summary: dict) -> str:
    e=lambda x:html.escape(str(x),quote=True)
    rows=''.join(f'<tr><td>{e(x["label"])} / {x["step"]}</td><td class="{x["send"]}">{x["send"]}</td><td class="{x["adopt"]}">{x["adopt"]}</td><td>{"あり" if x["attempted"] else "なし"}</td><td>{x["units"]} / 3</td><td><a href="{e(x["record"])}">記録JSON</a></td></tr>' for x in summary['rows'])
    return '''<!doctype html><html lang="ja"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'"><title>PoC第2弾 実行結果</title><style>body{margin:0;background:#f3f5f6;color:#183641;font:14px/1.9 system-ui,sans-serif}main{max-width:1060px;margin:auto;padding:40px 22px}h1{font-size:32px}h2{font-size:20px}header{border-bottom:2px solid #163b47;padding-bottom:24px}p{max-width:900px}.note{background:white;border-left:4px solid #08796c;padding:15px 20px}table{width:100%;background:white;border-collapse:collapse}th,td{padding:12px;text-align:left;border-bottom:1px solid #dce4e8;font-size:12px}.scroll{overflow:auto}.PASS{color:#067b63;font-weight:700}.HOLD{color:#9c6a15;font-weight:700}.REJECT{color:#b54044;font-weight:700}a{color:#067b63}footer{margin-top:25px;color:#647a84;font-size:12px}</style><main><header><small>PRIVACY ASSURANCE · PHASE 02 · SYNTHETIC ONLY</small><h1>情報を使いながら、<br>許されない処理を止める。</h1><p>Pythonが実行したローカル模擬送信・出力採用・累積開示の結果です。送信判定と出力採用判定を分けて表示します。</p></header>'''+f'''<p class="note"><b>保存記録・実ファイルの再検証 {summary['records_verified']} / {summary['records_verified']}、自己テスト {summary['self_tests']} / {summary['self_tests']}</b><br>点数は固定項目に対するデモ制約です。匿名性・再識別確率・法令適合を証明するものではありません。</p><h2>判定と実行の内訳</h2><div class="scroll"><table><tr><th>ケース</th><th>送信</th><th>出力採用</th><th>模擬送信</th><th>累積点数</th><th>証拠</th></tr>{rows}</table></div><footer>実住民情報・外部AI・実際の外部通信は使用していません。模擬送信先のoutboxはこの実行フォルダ内のファイルです。<br>Copyright © 2026 AI Assurance, Inc. All rights reserved.</footer></main></html>'''


def conformance_samples(engine: Engine) -> list[tuple[dict,dict]]:
    """判定結果を観測入力へ流用せず、元の要求と台帳を組み立てる。"""
    samples=[]
    for t in engine.tests.values():
        samples.append((engine.request(t['changes'],'TEST-'+t['key']),engine.state(t['seed'])))
    for sc in engine.data['scenarios']:
        session=Session(engine)
        for r,_,_ in engine.scenario_requests(sc['key']):
            samples.append((r,copy.deepcopy(session.state)))
            session.execute(r)
    fs=list(engine.policy['fields'])
    subsets=[[k for k,b in zip(fs,bits) if b] for bits in itertools.product([False,True],repeat=len(fs))]
    for fields,prior in itertools.product(subsets,subsets):
        samples.append((engine.request({'fields':fields},'FIELDS-CHECK'),engine.state({'disclosed':prior})))
    for basis,role_ok,recipient_ok,terms_known,history_known,pending,duplicate in itertools.product(
            ['confirmed','missing','denied'],*[ [False,True] for _ in range(6)]):
        r=engine.request({'basis':basis,'role':'consultation_staff' if role_ok else 'OTHER',
                          'recipient':'MOCK-AI-JP' if recipient_ok else 'OTHER',
                          'terms':'confirmed' if terms_known else 'missing'},'CONTROL-CHECK')
        s=engine.state({'known':history_known,'pending':pending,'used_ids':['CONTROL-CHECK'] if duplicate else []})
        samples.append((r,s))
    for mode,ack in itertools.product(sorted(RESPONSE_MODES),['ack','unknown']):
        samples.append((engine.request({'response':mode,'outcome':ack},'OUTPUT-CHECK'),engine.state()))
    return samples


def browser_script() -> str:
    text=(ROOT/'civic_privacy_poc_demo.html').read_text(encoding='utf8')
    matches=re.findall(r'<script id="privacy-engine">(.*?)</script>',text,re.S)
    require(len(matches)==1,'HTMLの共有検証エンジンが見つかりません。')
    return matches[0]


def check_javascript(engine: Engine, samples: list[tuple[dict,dict]], temp: Path) -> int:
    require(shutil.which('node') is not None,'JavaScript照合にはNode.jsが必要です（通常のPoC実行には不要）。')
    source=browser_script()
    text=(ROOT/'civic_privacy_poc_demo.html').read_text(encoding='utf8')
    embedded=re.search(r'<script id="privacy-data" type="application/json">(.*?)</script>',text,re.S)
    require(embedded is not None and canonical(parse_json(embedded.group(1)))==canonical(engine.data),'HTML同梱データとcases.jsonが一致しません。')
    code=temp/'engine.js';code.write_text(source,encoding='utf8')
    expected=[]
    for r,s in samples:
        result=engine.simulate(r,s)
        expected.append({'request':r,'state':s,'result':result,'packet':engine.packet(r,s,result)})
    data=temp/'parity.json';write_json(data,{'data':engine.data,'expected':expected})
    checker=r'''
const fs=require('fs'),vm=require('vm');
const c={TextEncoder,console};vm.createContext(c);vm.runInContext(fs.readFileSync(process.argv[2],'utf8'),c);
const d=JSON.parse(fs.readFileSync(process.argv[3],'utf8')),D=c.PrivacyDemo,E=new D.Engine(d.data);
for(const t of d.expected){let r=E.simulate(t.request,t.state);if(D.canonical(r)!==D.canonical(t.result))throw Error('Python/JS result mismatch: '+t.request.request_id);
 let p=E.packet(t.request,t.state,r);if(D.canonical(p)!==D.canonical(t.packet)||!E.verify(p).ok)throw Error('Python/JS packet mismatch');}
for(const sc of d.data.scenarios){const s=new D.Session(E);for(const [r,es,ea] of E.scenarioRequests(sc.key)){let p=s.execute(r);if(p.payload.result.send.decision!==es||p.payload.result.adoption.decision!==ea)throw Error('Sequence mismatch');}if(s.received.length!==s.records.filter(p=>p.payload.result.attempted).length)throw Error('Mock gate mismatch');}
for(const text of ['{"a":1,"a":2}','{"x":NaN}','{"x":0.5}','{"x":-1}','{"x":"\\ud800"}']){let blocked=false;try{D.parseJson(text);}catch(e){blocked=true;}if(!blocked)throw Error('Invalid JSON accepted');}
console.log('Python/JavaScript full-result and packet conformance: '+d.expected.length+' / '+d.expected.length);
'''
    runner=temp/'check.js';runner.write_text(checker,encoding='utf8')
    subprocess.run(['node',str(runner),str(code),str(data)],check=True)
    return len(expected)


def lean_structure(values: dict) -> str:
    def val(v):
        if type(v) is bool:return 'true' if v else 'false'
        require(type(v) is int and v>=0,'Leanへの観測型が不正です。')
        return str(v)
    return '{ '+', '.join(k+' := '+val(v) for k,v in values.items())+' }'


def proof_groups(engine: Engine, samples: list[tuple[dict,dict]]):
    """小さい独立命題。定義と証明を同じバッチに置き、巨大な一括評価を避ける。"""
    for i,(r,s) in enumerate(samples):
        x=engine.observations(r,s); res=engine.simulate(r,s)
        o=engine.output_observations(r,res['wire'],res['response'],res['attempted'])
        statuses='['+', '.join('Status.'+c['status'] for c in res['send']['checks'])+']'
        name='sample_'+str(i);out='output_'+str(i);th='matches_'+str(i)
        expected=f'({statuses}, Status.{res["send"]["decision"]}, Status.{res["adoption"]["decision"]}, {res["units_after"]}, {str(res["after"]["pending"]).lower()})'
        group = [f'def {name} : Input := {lean_structure(x)}', f'def {out} : OutputObservation := {lean_structure(o)}',
            f'theorem {th} : (checks {name}, decision {name}, adoption {name} {out}, afterUnits {name}, pendingAfter {name} {out}.acknowledged) = {expected} := by decide',
            f'#print axioms Conformance.{th}']
        # The 59 published test/sequence records also exercise the abstract record view.
        # Change one semantic field, recompute the hash, and compare Python/Lean rejection.
        if i < 59:
            for j in range(5):
                edited=copy.deepcopy(res)
                if j==1: edited['send']['decision']='HOLD' if res['send']['decision']=='PASS' else 'PASS'
                if j==2: edited['adoption']['decision']='HOLD' if res['adoption']['decision']=='PASS' else 'PASS'
                if j==3: edited['units_after']+=1
                if j==4: edited['after']['pending']=not edited['after']['pending']
                packet=engine.packet(r,s,edited); verdict=engine.verify(packet)
                view=('{ evidenceOK := '+str(verdict['intact'] and verdict['specification']).lower()+
                      ', recordedSend := Status.'+edited['send']['decision']+
                      ', recordedAdoption := Status.'+edited['adoption']['decision']+
                      ', recordedUnits := '+str(edited['units_after'])+
                      ', recordedPending := '+str(edited['after']['pending']).lower()+' }')
                rn=f'record_{i}_{j}'
                group += [f'theorem {rn} : reverify {name} {out} ({view}) = {str(verdict["ok"]).lower()} := by decide',
                          f'#print axioms Conformance.{rn}']
        yield group
    for i,vector in enumerate(itertools.product(STATUSES,repeat=8)):
        xs='['+', '.join('Status.'+s for s in vector)+']';th='aggregate_'+str(i)
        yield [f'theorem {th} : worst {xs} = Status.{worst(list(vector))} := by decide',f'#print axioms Conformance.{th}']


def audit_dependencies(output: str, names: list[str]) -> None:
    for name in names:
        require(name in output,'公理監査の出力が欠落：'+name)
    allow={'propext','Quot.sound','Classical.choice'}
    for dep in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output):
        unknown={x.strip() for x in dep.split(',') if x.strip()}-allow
        require(not unknown,'未承認の証明依存：'+repr(unknown))
    require(not any(x in output for x in ['sorryAx','Lean.ofReduceBool','Lean.trustCompiler']),'未承認の証明依存です。')


def check_lean(engine: Engine, samples: list[tuple[dict,dict]], temp: Path) -> dict:
    require(shutil.which('lake') is not None,'Lean/Lakeがありません。READMEの検査環境またはGitHub Actionsで実行してください。')
    source=(ROOT/'CivicPrivacyAssurance.lean').read_text(encoding='utf8')
    require(not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',source),'未証明宣言または独自公理を検出しました。')
    require(re.findall(r'(?m)^import\s+(.+)$',source)==['Std'],'Leanのインポート構成をレビューしてください。')
    names=re.findall(r'(?m)^theorem\s+([A-Za-z_][A-Za-z_0-9]*)',source)
    require(len(names)==55,'中核定理の数が変わっています。証明範囲を確認してください。')
    version=subprocess.run(['lake','env','lean','--version'],cwd=ROOT,text=True,capture_output=True,check=True).stdout
    require('4.19.0' in version,'この版はLean 4.19.0で固定しています。')
    subprocess.run(['lake','update'],cwd=ROOT,check=True)
    subprocess.run(['lake','build'],cwd=ROOT,check=True)
    def check(name,body,expected_names):
        file=temp/name;file.write_text(body,encoding='utf8')
        result=subprocess.run(['lake','env','lean','-DwarningAsError=true',str(file)],cwd=ROOT,
                              text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout,flush=True)
            raise InputError('Lean検査が失敗しました：'+name)
        audit_dependencies(result.stdout,expected_names)
    check('ModelAxioms.lean','import CivicPrivacyAssurance\n'+'\n'.join('#print axioms CivicPrivacyAssurance.'+n for n in names),['CivicPrivacyAssurance.'+n for n in names])
    header='import CivicPrivacyAssurance\nset_option warningAsError true\nset_option maxRecDepth 2048\nset_option maxHeartbeats 1000000\nopen CivicPrivacyAssurance\nnamespace Conformance\n'
    fixed=f'example : referenceSHA256 = "{REFERENCE_SHA256}" := by decide\n'
    pending=[];batches=0;count=0;size=0
    def flush():
        nonlocal pending,batches,size
        if not pending:return
        lines=[line for group in pending for line in group]
        expected=[line.split()[-1] for line in lines if line.startswith('#print axioms ')]
        check(f'Batch{batches:04d}.lean',header+fixed+'\n\n'.join(lines)+'\nend Conformance\n',expected)
        batches+=1;pending=[];size=0
    for group in proof_groups(engine,samples):
        n=sum(len(line.encode('utf8')) for line in group)
        if pending and (len(pending)>=32 or size+n>48000):flush()
        pending.append(group);size+=n;count+=1
    flush()
    require(count==len(samples)+3**8,'具体命題の検査数が不足しています。')
    return {'model_theorems':len(names),'projected_cases':len(samples),'aggregator_vectors':3**8,'record_view_checks':295,'batches':batches,'lean_checked':True}


def ci(engine: Engine) -> dict:
    tests=self_tests(engine)
    require(all(t['passed'] for t in tests),'Python自己テストが失敗しています。')
    (ROOT/'.lake').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='privacy-ci-',dir=ROOT/'.lake') as d:
        temp=Path(d)
        # 実ファイルの書き出しと再検証をCIでも省略しない。
        run(engine,temp/'execution')
        samples=conformance_samples(engine)
        js=check_javascript(engine,samples,temp)
        checked_model=check_lean(engine,samples,temp)
    result={'self_tests':len(tests),'javascript_conformance':js,**checked_model}
    print(json.dumps(result,ensure_ascii=False,indent=2))
    return result


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--data',type=Path,default=ROOT/'cases.json')
    parser.add_argument('--out',type=Path,default=ROOT/'output')
    commands=parser.add_subparsers(dest='command')
    commands.add_parser('run',help='全ケースを実行')
    demo=commands.add_parser('demo',help='連続シナリオを実行');demo.add_argument('scenario')
    commands.add_parser('test',help='Python自己テスト')
    verify=commands.add_parser('verify',help='記録・実行フォルダを再検証');verify.add_argument('path',type=Path)
    commands.add_parser('ci',help='Python/JavaScript/Leanの全検査。Lean不在時は失敗終了')
    for sub in commands.choices.values():
        sub.add_argument('--data',type=Path,default=argparse.SUPPRESS,help=argparse.SUPPRESS)
        sub.add_argument('--out',type=Path,default=argparse.SUPPRESS,help=argparse.SUPPRESS)
    args=parser.parse_args()
    try:
        engine=Engine(read_json(args.data));command=args.command or 'run'
        if command=='test':
            rows=self_tests(engine)
            for r in rows:
                if not r['passed']:print(r,file=sys.stderr)
            print(f"Python自己テスト：{sum(r['passed'] for r in rows)} / {len(rows)}")
            return 0 if all(r['passed'] for r in rows) else 1
        if command=='ci':
            report=ci(engine)
            import os
            if os.environ.get('GITHUB_STEP_SUMMARY'):
                with open(os.environ['GITHUB_STEP_SUMMARY'],'a',encoding='utf8') as f:
                    f.write('### Privacy assurance verification\n\n```json\n'+json.dumps(report,indent=2)+'\n```\n')
            return 0
        if command=='verify':
            p=args.path
            if p.is_file():
                result=engine.verify(read_json(p));print(json.dumps(result,ensure_ascii=False,indent=2));return 0 if result['ok'] else 1
            roots=[p] if (p/'index.json').is_file() else sorted(f.parent for f in p.glob('run-*/index.json'))
            require(bool(roots),'実行フォルダがありません。')
            count=sum(verify_folder(engine,r) for r in roots);print(f'記録・模擬受信・採用文案の再検証：{count}件成立');return 0
        run(engine,args.out,args.scenario if command=='demo' else None)
        return 0
    except (InputError,OSError,UnicodeError,KeyError,TypeError,RecursionError,subprocess.CalledProcessError) as e:
        print(f'入力・実行・検査エラー：{e}\n検査成功として扱わないでください。',file=sys.stderr)
        return 2

if __name__=='__main__':
    for stream in (sys.stdout,sys.stderr):
        if hasattr(stream,'reconfigure'):stream.reconfigure(encoding='utf-8',errors='replace')
    raise SystemExit(main())
