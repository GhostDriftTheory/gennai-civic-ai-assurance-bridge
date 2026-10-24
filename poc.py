#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright © 2026 AI Assurance, Inc. All rights reserved. See README.md.
"""源内公開API仕様 × 自治体AIアシュアランス3機能（固定合成データ専用）。

python poc.py                 # run 31 scenarios; no external service or key
python poc.py test            # original regressions + integration tests
python poc.py verify PATH     # replay saved records, not authenticity certification
python poc.py serve           # localhost UI + synchronous inputs/outputs REST API
python poc.py ci              # strict: requires Lean and Node; never silently skips

Existing sources and evidence are never edited. The answer/, privacy/ and
lifecycle/ directories contain locked, byte-exact public source copies. No ZIP
or extraction step is necessary. The shared profile binds their functionality.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import hmac
import html
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any

ROOT = Path(__file__).resolve().parent
PROFILE_HASH = '51c5598cfce00bee6fc9742259382f6173ddb5d17eec0690582b04dca55bcedd'
VERSION = '1.0.1'
STATUSES = ('PASS', 'HOLD', 'REJECT')
NOT_RUN = 'NOT_RUN'
MAX_JSON_BYTES = 32 * 1024 * 1024
HTTP_MAX_BYTES = 65536
SCOPE = {
    'synthetic_only': True, 'provider': 'local-synthetic-fixture',
    'external_ai_calls': 0, 'gennai_hosted_environment_tested': False,
    'gennai_oss_ui_tested': False, 'protocol': 'sync-inputs-outputs',
    'government_endorsement': False, 'legal_compliance_certification': False,
    'termination': 'registered-local-business-routes-only',
    'audit_evidence_retained': True, 'signature_or_trusted_time': False,
}


class InputError(ValueError):
    """Bad input or evidence, not a successful business decision."""


def require(ok: bool, message: str) -> None:
    if not ok:
        raise InputError(message)


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(',', ':'), allow_nan=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode('utf-8')).hexdigest()


def filehash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_tree(value: Any, depth: int = 0) -> None:
    require(depth <= 70, 'JSON nesting is too deep')
    if value is None or type(value) in (bool, str):
        if type(value) is str:
            require(len(value) <= 1_000_000, 'String too long')
            try:
                value.encode('utf-8')
            except UnicodeError as exc:
                raise InputError('Invalid Unicode') from exc
        return
    if type(value) is int:
        require(abs(value) <= 9007199254740991, 'Integer outside safe range')
        return
    if type(value) is float:
        require(math.isfinite(value) and abs(value) <= 9007199254740991, 'Invalid numeric value')
        return
    if type(value) is list:
        require(len(value) <= 20000, 'Array too long')
        for item in value:
            validate_tree(item, depth + 1)
        return
    require(type(value) is dict and len(value) <= 20000, 'Invalid JSON object')
    for key, item in value.items():
        require(type(key) is str, 'Non-string object key')
        validate_tree(key, depth + 1)
        validate_tree(item, depth + 1)


def parse_json(text: str) -> Any:
    require(type(text) is str and len(text.encode('utf-8')) <= MAX_JSON_BYTES, 'Oversized JSON')
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    def bad_number(value):
        raise InputError('Non-finite JSON number: ' + value)
    try:
        result = json.loads(text, object_pairs_hook=pairs, parse_constant=bad_number)
        validate_tree(result)
        return result
    except (UnicodeError, RecursionError, json.JSONDecodeError) as exc:
        raise InputError('Invalid JSON') from exc


def read_json(path: Path) -> Any:
    require(path.is_file() and path.stat().st_size <= MAX_JSON_BYTES, 'Missing/oversized JSON: ' + str(path))
    return parse_json(path.read_text(encoding='utf-8-sig'))


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp-' + uuid.uuid4().hex)
    try:
        with temporary.open('x', encoding='utf-8', newline='\n') as stream:
            json.dump(data, stream, ensure_ascii=False, indent=2, allow_nan=False)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def config() -> dict:
    value = read_json(ROOT / 'cases.json')
    require(digest(value) == PROFILE_HASH, 'Fixed shared profile or source lock changed; do not treat this as the reviewed version')
    return value


def prepare_dependencies(cfg: dict) -> None:
    """Validate all nine GitHub-uploaded source files, without ZIP or extraction."""
    expected_names = {
        f'{name}/{filename}'
        for name, model in [('answer', 'CivicAnswerAdoption.lean'),
                            ('privacy', 'CivicPrivacyAssurance.lean'),
                            ('lifecycle', 'CivicLifecycleAssurance.lean')]
        for filename in ('poc.py', 'cases.json', model)
    }
    require(set(cfg['upstream_files']) == expected_names,
            'Unexpected source manifest: exactly 9 direct files required')
    for name, lock in cfg['upstream_files'].items():
        rel = Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts and len(rel.parts) == 2,
                'Unsafe source path')
        source = ROOT / rel
        require(source.is_file() and not source.is_symlink() and not source.parent.is_symlink(),
                'Missing or unsafe source file: ' + name)
        require(source.stat().st_size == lock['size'], 'Unexpected source size: ' + name)
        require(filehash(source) == lock['sha256'], 'Source bytes changed: ' + name)


def source_binding(cfg: dict) -> dict:
    files = ['poc.py', 'cases.json', 'CivicBridge.lean', 'lean-toolchain', 'lakefile.toml']
    return {'version': VERSION, 'profile_sha256': PROFILE_HASH,
            'integration_files': {name: hashlib.sha256((ROOT / name).read_bytes().replace(b'\r\n', b'\n')).hexdigest() for name in files},
            'integration_text_normalization': 'CRLF-to-LF-only',
            'source_layout': 'direct-verified-folders', 'sources': cfg['sources']}


class Components:
    """Load three original modules under separate names; never monkey-patch them."""
    def __init__(self, cfg: dict):
        prepare_dependencies(cfg)
        self.modules = {}
        self.engines = {}
        for name in ('answer', 'privacy', 'lifecycle'):
            path = ROOT / name / 'poc.py'
            module_name = 'civic_bridge_upstream_' + name
            spec = importlib.util.spec_from_file_location(module_name, path)
            require(spec is not None and spec.loader is not None, 'Cannot load source')
            module = importlib.util.module_from_spec(spec)
            sys.modules[module_name] = module
            raw = path.read_bytes()
            require(hashlib.sha256(raw).hexdigest() == cfg['upstream_files'][name + '/poc.py']['sha256'],
                    'Source changed before execution')
            exec(compile(raw, str(path), 'exec'), module.__dict__)  # Never trust a cached .pyc.
            self.modules[name] = module
            self.engines[name] = module.Engine(module.read_json(path.parent / 'cases.json'))


def compose(observation: dict) -> dict:
    """Finite composition model; input identities are derived, not model assertions."""
    keys = {'send', 'output', 'answer', 'same_request', 'same_answer', 'origins_bound',
            'registered', 'use', 'action_ok'}
    require(type(observation) is dict and set(observation) == keys, 'Invalid composition observation')
    for key in ('send', 'output', 'answer', 'use'):
        require(observation[key] in (*STATUSES, NOT_RUN), 'Unknown status')
    for key in keys - {'send', 'output', 'answer', 'use'}:
        require(type(observation[key]) is bool, 'Composition flags must be Boolean')
    eligible = (all(observation[k] == 'PASS' for k in ('send', 'output', 'answer'))
                and observation['same_request'] and observation['same_answer']
                and observation['origins_bound'])
    return {'may_register': eligible,
            'may_supply': eligible and observation['registered'] and observation['use'] == 'PASS'
                          and observation['action_ok']}


class PrivacyAdapter:
    """New subsidy profile, original P2 8/4-check aggregation, no P2 policy mutation.

    Only the observation boundary and explanatory labels are new. This is not a
    claim that the original fixed childcare fixture accepts arbitrary inputs.
    """
    def __init__(self, profile: dict, original_module: Any, expected_wire: dict):
        self.profile = profile
        self.module = original_module
        self.expected_wire = expected_wire
        self.policy = {'gate_names': profile['privacy_gate_names'],
                       'output_gate_names': profile['output_gate_names']}

    def observations(self, request: dict, state: dict) -> dict:
        wire = request['wire']
        fields = set(wire['applicant'])
        new = fields - set(state['disclosed'])
        weights = self.profile['fields']
        return {
            'sourceOK': request['case_id'] == wire['case_id'] == state['case_id'],
            'scopeOK': request['purpose'] == self.profile['purpose'] and request['human_confirmation'] is True,
            'authorityKnown': request['basis'] != 'missing',
            'authorityOK': request['basis'] == 'confirmed' and request['role'] == self.profile['role'],
            'termsKnown': True,
            'recipientOK': request['recipient'] == self.profile['recipient'],
            'termsOK': request['retention_days'] == 0 and request['training'] is False,
            'fieldsOK': fields == set(weights) and set(wire) == {'case_id', 'target', 'as_of', 'applicant', 'sources'},
            'evidenceKnown': True,
            'payloadOK': wire == self.expected_wire,
            'ledgerKnown': state['known'], 'pending': state['pending'],
            'duplicate': request['request_id'] in state['used_ids'],
            'used': sum(weights.get(k, 0) for k in state['disclosed']),
            'additional': sum(weights.get(k, 0) for k in new), 'limit': request['limit'],
        }

    def evaluate(self, request: dict, state: dict) -> dict:
        result = self.module.Engine.evaluate(self, request, state)
        # Source P2 includes fixed childcare explanations; do not mislabel the new profile.
        notes = ['共通案件IDと管理台帳の対象を照合。', '補助金案内・職員確認用の用途を照合。',
                 '固定合成シナリオの利用根拠と模擬権限を照合。', 'ローカル合成生成器と取扱条件を照合。',
                 '相談条件4項目だけを送信対象とする。氏名・住所は対象外。', '判定対象と受信器へ渡すデータの完全一致を照合。',
                 '同一合成対象について、既開示項目と新規項目のデモ点数を集計。', '未確定要求と同一要求IDの再実行を止める。']
        for check, note in zip(result['checks'], notes):
            check['detail'] = note
        return result

    def output_observations(self, request: dict, wire: dict, response: dict | None, attempted: bool) -> dict:
        available = type(response) is dict
        candidate = response.get('candidate') if available else None
        shape = (available and set(response) == {'request_digest', 'case_id', 'candidate', 'claimed_conditions'}
                 and type(candidate) is dict and set(candidate) == {'program_id', 'claims', 'text'}
                 and type(candidate.get('text')) is str and type(candidate.get('claims')) is dict)
        public = canonical(candidate) if type(candidate) is dict else ''
        return {
            'available': available and attempted,
            'acknowledged': available and attempted,
            'bindingKnown': available and response.get('request_digest') is not None,
            'bindingOK': available and response.get('request_digest') == digest(wire)
                         and response.get('case_id') == wire['case_id'],
            'fieldsOK': bool(shape),
            'textOK': bool(shape) and all(value not in public for value in self.profile['private'].values()),
            'useOK': request['human_confirmation'] is True,
        }

    def evaluate_output(self, request: dict, wire: dict, response: dict | None, attempted: bool) -> dict:
        result = self.module.Engine.evaluate_output(self, request, wire, response, attempted)
        notes = ['受信した応答の案件ID・要求内容識別値を照合。', '構造化回答の許可された項目を検査。',
                 '固定合成の氏名・住所が再混入していないか検査。自由文一般の個人情報検出ではない。',
                 '職員確認用の案内文。受給決定や自動対外送信は許可しない。']
        for check, note in zip(result['checks'], notes):
            check['detail'] = note
        return result


class BoundGenerator:
    """P3 provider port: reuse the EXACT already-checked answer, not a second answer."""
    def __init__(self, module: Any, texts: list[str], answer: str):
        self.module, self.texts, self.answer = module, texts, answer
        self.calls = 0

    def generate(self, request: dict) -> dict:
        require(request['input_objects'] == ['A', 'B'] and request['texts'] == self.texts,
                'Lifecycle input substituted')
        require(request['input_digests'] == [self.module.digest(t) for t in self.texts],
                'Lifecycle content binding mismatch')
        self.calls += 1
        return {'request_id': request['request_id'], 'provider': 'mock', 'outcome': 'completed',
                'text': self.answer, 'claimed_conditions': []}


def lifecycle_commands(mode: str) -> list[dict]:
    def use(purpose='consultation', recipient='internal'):
        return {'op': 'use', 'actor': 'staff', 'target': 'S', 'purpose': purpose, 'recipient': recipient}
    if mode == 'read':
        return [use()]
    if mode == 'secondary':
        return [use('secondary')]
    if mode == 'approve_secondary':
        return [{'op': 'approve', 'actor': 'reviewer', 'target': 'S', 'approval': 'G1'},
                {'op': 'amend', 'actor': 'reviewer', 'target': 'S', 'approval': 'G1'}, use('secondary')]
    if mode == 'external':
        return [use(recipient='external')]
    if mode == 'expired':
        return [{'op': 'tick', 'actor': 'operator', 'time': 10}, use()]
    if mode == 'unknown_path':
        return [{'op': 'route_unknown', 'actor': 'operator', 'path': 'S-read'}, use()]
    if mode in ('copy_left', 'closed', 'stale_certificate'):
        commands = [
            {'op': 'copy', 'actor': 'staff', 'source': 'S', 'target': 'C'},
            {'op': 'freeze', 'actor': 'operator', 'origin': 'O-A'},
            {'op': 'close', 'actor': 'operator', 'path': 'A-read'},
            {'op': 'close', 'actor': 'operator', 'path': 'S-read'},
        ]
        if mode != 'copy_left':
            commands.append({'op': 'close', 'actor': 'operator', 'path': 'C-read'})
        commands.append({'op': 'certify', 'origin': 'O-A', 'scope': 'local-business',
                         'audit_exception': True, 'certificate': 'T1'})
        if mode == 'stale_certificate':
            commands += [{'op': 'route_restore', 'actor': 'operator', 'path': 'S-read'},
                         {'op': 'apply_certificate', 'certificate': 'T1'}]
        return commands
    raise InputError('Unknown lifecycle scenario')


class Bridge:
    def __init__(self):
        self.cfg = config()
        self.c = Components(self.cfg)
        self.binding = source_binding(self.cfg)
        self.profile = self.cfg['profile']
        self.scenarios = {s['key']: s for s in self.cfg['scenarios']}
        self._lock = threading.RLock()

    def wire(self, scenario: dict) -> dict:
        base = self.c.engines['answer'].base()
        app = {k: copy.deepcopy(base['applicant'][k]) for k in self.profile['fields']}
        app.update(copy.deepcopy(scenario['applicant']))
        require(set(app) == set(self.profile['fields']), 'Unknown common-profile field')
        return {'case_id': 'SYN-BRIDGE-01', 'target': base['target'], 'as_of': base['as_of'],
                'applicant': app, 'sources': base['sources']}

    def answer_input(self, wire: dict, candidate: dict) -> dict:
        base = self.c.engines['answer'].base()
        base['id'], base['label'] = wire['case_id'], '共通合成シナリオ・補助金案内'
        base['target'], base['as_of'] = copy.deepcopy(wire['target']), wire['as_of']
        base['sources'] = copy.deepcopy(wire['sources'])
        base['applicant'].update(copy.deepcopy(wire['applicant']))
        base['question'] = '提示した合成条件で、公開サンプル制度の案内を作成する。'
        base['candidate'] = copy.deepcopy(candidate)
        return base

    def receiver(self, wire: dict, mode: str) -> dict:
        """Deterministic fixture; cannot access the excluded private source fields.
        Test mutations are explicit fixture modes, not measures of real AI quality.
        """
        m, engine = self.c.modules['answer'], self.c.engines['answer']
        candidate = copy.deepcopy(engine.base()['candidate'])
        candidate['claims']['eligibility']['value'] = engine.eligibility(wire['applicant'])
        if mode == 'wrong_city': candidate['claims']['municipality']['value'] = '自治体Y'
        if mode == 'wrong_amount': candidate['claims']['max_yen']['value'] = 600000
        if mode == 'missing_citation':
            candidate['claims']['max_yen']['source_id'] = None
            candidate['claims']['max_yen']['section'] = None
            candidate['claims']['max_yen']['source_hash'] = None
        candidate['text'] = m.build_text(candidate['claims'])
        if mode == 'unexpected_prose': candidate['text'] += '\n今すぐ自動決定してください。'
        if mode == 'private_output': candidate['text'] += '\n架空相談者A様。'
        return {'request_digest': None if mode == 'missing_binding' else '0' * 64 if mode == 'wrong_binding' else digest(wire),
                'case_id': wire['case_id'], 'candidate': candidate,
                'claimed_conditions': [] if mode == 'model_relaxes' else None}

    def run_case(self, key: str) -> dict:
        # Original provider ports are per-run; serialize access in this reference process.
        with self._lock:
            return self._run_case(key)

    def _run_case(self, key: str) -> dict:
        require(type(key) is str and key in self.scenarios, 'Unknown scenario')
        scene = self.scenarios[key]
        original = self.wire(scene)
        expected_wire = copy.deepcopy(original)
        wire = copy.deepcopy(original)
        privacy_changes = scene['privacy']
        if privacy_changes.get('add_private'):
            wire['applicant']['resident_name'] = self.profile['private']['resident_name']
        if privacy_changes.get('patch_wire'):
            wire['applicant']['employees'] = 9
        if scene['answer'] == 'stale_source':
            # An explicitly changed input fixture, not an invisible update of the reference catalog.
            wire['sources'][0]['version'] = 'old-untrusted-version'
            expected_wire = copy.deepcopy(wire)
        adapter = PrivacyAdapter(self.profile, self.c.modules['privacy'], expected_wire)
        request = {
            'request_id': 'SYN-REQUEST-01', 'case_id': wire['case_id'], 'wire': wire,
            'purpose': self.profile['purpose'], 'human_confirmation': True, 'role': 'staff',
            'basis': privacy_changes.get('basis', 'confirmed'),
            'recipient': privacy_changes.get('recipient', self.profile['recipient']),
            'training': False, 'retention_days': 0, 'limit': privacy_changes.get('limit', self.profile['budget']),
        }
        ledger = {'case_id': wire['case_id'], 'known': privacy_changes.get('history_known', True),
                  'pending': False, 'disclosed': [], 'used_ids': [], 'revision': 0}
        events, received = [], []
        previous = digest({'profile': PROFILE_HASH, 'scenario': key})
        def event(kind: str, details: dict):
            nonlocal previous
            body = {'sequence': len(events) + 1, 'previous': previous, 'kind': kind, 'data': copy.deepcopy(details)}
            previous = digest(body)
            events.append({'body': body, 'sha256': previous})
        send = adapter.evaluate(request, ledger)
        before = copy.deepcopy(ledger)
        observations = adapter.observations(request, ledger)
        response = None
        if send['decision'] == 'PASS':
            # Commit intent/consumption BEFORE the call. Unknown delivery never rolls it back.
            ledger['disclosed'] = sorted(set(ledger['disclosed']) | set(wire['applicant']))
            ledger['used_ids'].append(request['request_id'])
            ledger['revision'] += 1
            ledger['pending'] = True
            encoded = canonical(wire).encode('utf-8')
            actual_wire = parse_json(encoded.decode('utf-8'))
            received.append({'request_digest': digest(actual_wire), 'bytes_sha256': hashlib.sha256(encoded).hexdigest()})
            if privacy_changes.get('delivery') != 'unknown':
                response = self.receiver(actual_wire, scene['answer'])
                ledger['pending'] = False
        event('privacy.send', {'request': request, 'observation': observations, 'before': before,
                               'result': send, 'after': ledger, 'receiver_calls': len(received)})
        output, answer = NOT_RUN, NOT_RUN
        output_result = None
        same_request, same_answer, origins_bound = False, False, False
        action_status, action_name = send['decision'], '回答案の採用・利用'
        lifecycle_state, lifecycle_results = None, []
        accepted_hash, verified_text = None, None
        if send['decision'] == 'PASS':
            output_result = adapter.evaluate_output(request, wire, response, True)
            output = output_result['decision']
            same_request = bool(response and response['request_digest'] == digest(wire) and response['case_id'] == wire['case_id'])
            event('privacy.output', {'response': response, 'observation': adapter.output_observations(request, wire, response, True),
                                    'result': output_result})
            action_status = output
            if output == 'PASS':
                x = self.answer_input(wire, response['candidate'])
                result = self.c.engines['answer'].evaluate(x)
                answer = result['decision']
                event('answer.adoption', {'input': x, 'result': result})
                action_status = answer
                if answer == 'PASS':
                    verified_text = response['candidate']['text']
                    accepted_hash = digest(verified_text)
                    managed_text = verified_text + ('\n検証後の無許可変更。' if scene['answer'] == 'postcheck_tamper' else '')
                    same_answer = digest(managed_text) == accepted_hash
                    origins_bound = (wire['case_id'] == original['case_id']
                                     and digest(wire['sources']) == digest(self.c.engines['answer'].base()['sources']))
                    pre = {'send': send['decision'], 'output': output, 'answer': answer,
                           'same_request': same_request, 'same_answer': same_answer, 'origins_bound': origins_bound,
                           'registered': False, 'use': NOT_RUN, 'action_ok': True}
                    registration = compose(pre)
                    event('composition.registration', {'observation': pre, 'result': registration,
                                                       'checked_answer_sha256': accepted_hash, 'managed_answer_sha256': digest(managed_text)})
                    if not registration['may_register']:
                        action_status = 'REJECT'
                    else:
                        lm = self.c.modules['lifecycle']
                        le = self.c.engines['lifecycle']
                        # New adapter initial state. Only the two text values are substituted.
                        # Original origin conditions, actors, deadlines, transition logic stay intact.
                        lifecycle_state = le.initial()
                        lifecycle_state['objects']['A']['text'] = canonical(wire['applicant'])
                        lifecycle_state['objects']['B']['text'] = canonical({'target': wire['target'], 'sources': wire['sources']})
                        initial = copy.deepcopy(lifecycle_state)
                        texts = [lifecycle_state['objects'][k]['text'] for k in ('A', 'B')]
                        port = BoundGenerator(lm, texts, managed_text)
                        prior_provider = le.provider
                        le.provider = port
                        try:
                            commands = [{'op': 'derive', 'actor': 'staff', 'parents': ['A', 'B'],
                                         'target': 'S', 'support': 'unknown', 'mode': 'normal'}] + lifecycle_commands(scene['lifecycle'])
                            event('lifecycle.initial', {'wire_sha256': digest(wire), 'state': initial,
                                                      'initial_state_sha256': digest(initial), 'scope': self.profile['scope']})
                            for command in commands:
                                before_state = copy.deepcopy(lifecycle_state)
                                lifecycle_state, result = le.apply(lifecycle_state, command)
                                lifecycle_results.append(result)
                                event('lifecycle.operation', {'command': command, 'before_sha256': digest(before_state),
                                                              'after_sha256': digest(lifecycle_state), 'result': result})
                            require(port.calls == 1, 'Lifecycle must register exactly the checked answer once')
                        finally:
                            le.provider = prior_provider
                        action_status = lifecycle_results[-1]['status']
                        if scene['lifecycle'] in ('copy_left', 'closed'): action_name = '管理範囲の利用終了確認'
                        if scene['lifecycle'] == 'stale_certificate': action_name = '現在状態への終了証明の適用'
        if privacy_changes.get('duplicate') and received:
            retry_before = copy.deepcopy(ledger)
            retry_request = copy.deepcopy(request)
            # Unknown-result case uses a NEW request ID to demonstrate pending-state blocking.
            if ledger['pending']:
                retry_request['request_id'] = 'SYN-REQUEST-02'
            retry_result = adapter.evaluate(retry_request, ledger)
            require(retry_result['decision'] != 'PASS', 'Unsafe retry allowed')
            event('privacy.retry', {'request': retry_request, 'before': retry_before,
                                   'observation': adapter.observations(retry_request, ledger), 'result': retry_result,
                                   'after': ledger, 'receiver_calls': len(received)})
            action_status = retry_result['decision']
        registered = lifecycle_state is not None and 'S' in lifecycle_state['objects']
        use_status, current_text = NOT_RUN, None
        if registered:
            lm, le = self.c.modules['lifecycle'], self.c.engines['lifecycle']
            obj = lifecycle_state['objects']['S']
            same_answer = accepted_hash == digest(obj['text'])
            # Preserve the actual origins, including unchanged restrictions from origin B.
            expected_terms = lm.unique_terms([t for parent in ('A', 'B')
                                               for t in lifecycle_state['objects'][parent]['conditions']])
            if any(r['operation'] == 'amend' and r['status'] == 'PASS' for r in lifecycle_results):
                grant = le.ref['grant_scope']
                old_term = {'origin': grant['origin'], 'kind': grant['kind'], 'value': grant['from']}
                expected_terms = [{**t, 'value': grant['to']} if t == old_term else t for t in expected_terms]
            origins_bound = (obj['parents'] == ['A', 'B'] and obj['origins'] == ['O-A', 'O-B']
                             and lm.unique_terms(obj['conditions']) == lm.unique_terms(expected_terms))
            requested = lifecycle_results[-1]
            if requested['operation'] == 'use':
                use_status = requested['status']
                if requested['released'] is not None:
                    current_text = requested['released']['text']
        observation = {'send': send['decision'], 'output': output, 'answer': answer,
                       'same_request': same_request, 'same_answer': same_answer, 'origins_bound': origins_bound,
                       'registered': registered, 'use': use_status, 'action_ok': action_status == 'PASS'}
        permits = compose(observation)
        emitted = current_text if permits['may_supply'] else None
        if emitted is not None:
            require(digest(emitted) == accepted_hash, 'Supplied answer differs from checked answer')
        event('composition.supply', {'observation': observation, 'result': permits,
                                    'emitted_sha256': digest(emitted) if emitted is not None else None})
        payload = {'schema': 'gennai-civic-bridge-record/1.0', 'scenario': key, 'label': scene['label'],
                   'source_binding': self.binding, 'scope': SCOPE, 'wire': wire,
                   'events': events, 'receiver_calls': received, 'ledger': ledger,
                   'lifecycle_state': lifecycle_state,
                   'summary': {'send': send['decision'], 'output': output, 'answer': answer,
                               'action': action_name, 'decision': action_status,
                               'registered': registered, 'supplied': permits['may_supply'],
                               'lifecycle': lifecycle_results[-1]['status'] if lifecycle_results else NOT_RUN,
                               'local_receiver_calls': len(received), 'external_ai_calls': 0,
                               'pending': ledger['pending'], 'used_units': sum(self.profile['fields'].get(k, 0) for k in ledger['disclosed']),
                               'answer_text': emitted, 'observation': observation,
                               'termination_confirmed': bool(lifecycle_results and lifecycle_results[-1]['operation'] == 'certify'
                                                             and lifecycle_results[-1]['status'] == 'PASS')}}
        return {'payload': payload, 'sha256': digest(payload)}

    def verify(self, record: dict) -> dict:
        validate_tree(record)
        require(type(record) is dict and set(record) == {'payload', 'sha256'}, 'Invalid record envelope')
        p = record['payload']
        require(type(p) is dict and p.get('schema') == 'gennai-civic-bridge-record/1.0', 'Unknown evidence schema')
        require(p.get('source_binding') == self.binding, 'Record belongs to a different source/profile version')
        require(type(p.get('scenario')) is str and p['scenario'] in self.scenarios, 'Unknown evidence scenario')
        expected = self.run_case(p['scenario'])
        intact = digest(p) == record['sha256']
        same = record == expected
        return {'ok': intact and same, 'intact': intact, 'replayed': same,
                'decision': expected['payload']['summary']['decision'],
                'scope': 'fixed-synthetic-execution-consistency; not issuer authentication or present-world observation'}

    def all_records(self) -> dict:
        return {'schema': 'gennai-civic-bridge-evidence/1.0', 'source_binding': self.binding,
                'records': [self.run_case(key) for key in self.scenarios]}

    def verify_document(self, value: dict) -> int:
        if 'payload' in value:
            require(self.verify(value)['ok'], 'Record replay failed')
            return 1
        require(set(value) == {'schema', 'source_binding', 'records'} and value['schema'] == 'gennai-civic-bridge-evidence/1.0',
                'Invalid evidence collection')
        require(value['source_binding'] == self.binding, 'Evidence collection source mismatch')
        require(type(value['records']) is list and [r.get('payload', {}).get('scenario') for r in value['records']] == list(self.scenarios),
                'Missing, duplicated, reordered, or extra scenario records')
        for record in value['records']:
            require(self.verify(record)['ok'], 'A scenario did not replay')
        return len(value['records'])

    def registration(self) -> dict:
        return {'scenario': {'type': 'select', 'title': '合成検証シナリオ', 'required': True,
                             'desc': '実住民情報は入力しないでください。全ケースは独立した合成実験です。',
                             'items': [{'title': s['label'], 'value': s['key']} for s in self.scenarios.values()],
                             'default_value': 'normal'}}

    def invoke(self, body: dict) -> tuple[dict, dict]:
        require(type(body) is dict and set(body) == {'inputs'}, 'Expected only inputs')
        require(type(body['inputs']) is dict and set(body['inputs']) == {'scenario'}, 'Expected only inputs.scenario')
        key = body['inputs']['scenario']
        require(type(key) is str and key in self.scenarios, 'Unknown scenario')
        record = self.run_case(key)
        summary = record['payload']['summary']
        # Do not leak a rejected, unverified, or retired draft through the normal outputs field.
        text = f"## {record['payload']['label']}\n\n**{summary['action']}：{summary['decision']}**\n\n"
        text += f"送信 {summary['send']} / 出力情報検査 {summary['output']} / 回答採用 {summary['answer']}\n\n"
        text += summary['answer_text'] if summary['supplied'] else 'この操作では回答本文を出力しません。'
        text += '\n\n記録ID：`' + record['sha256'] + '`\n\n固定合成データの検証です。行政決定・本番導入・政府認定を意味しません。'
        return {'outputs': text}, record


def all_composition_inputs():
    for statuses in itertools.product((*STATUSES, NOT_RUN), repeat=4):
        for flags in itertools.product((False, True), repeat=5):
            yield dict(zip(('send', 'output', 'answer', 'use'), statuses),
                       **dict(zip(('same_request', 'same_answer', 'origins_bound', 'registered', 'action_ok'), flags)))


def run_tests(bridge: Bridge) -> dict:
    rows = []
    def check(name, action):
        try:
            require(action() is True, 'Expectation not met')
            rows.append({'name': name, 'passed': True})
        except Exception as exc:
            rows.append({'name': name, 'passed': False, 'error': type(exc).__name__ + ': ' + str(exc)})
    def rejected(action):
        try:
            result = action()
            return type(result) is dict and result.get('ok') is False
        except (InputError, ValueError, KeyError, TypeError, RecursionError):
            return True
    upstream = {}
    for name in ('answer', 'privacy', 'lifecycle'):
        tests = bridge.c.modules[name].self_tests(bridge.c.engines[name])
        upstream[name] = {'total': len(tests), 'passed': sum(t['passed'] for t in tests)}
        for test in tests:
            check('upstream/' + name + '/' + test['name'], lambda test=test: test['passed'] is True)
    records = {key: bridge.run_case(key) for key in bridge.scenarios}
    for key, record in records.items():
        p, s = record['payload'], record['payload']['summary']
        check(key + '/expected', lambda key=key, s=s: s['decision'] == bridge.scenarios[key]['expected'])
        check(key + '/replay', lambda r=record: bridge.verify(r)['ok'])
        check(key + '/supply_gate', lambda s=s: (s['answer_text'] is not None) == s['supplied'] == compose(s['observation'])['may_supply'])
        check(key + '/no_external_ai', lambda p=p: p['scope']['external_ai_calls'] == 0 and p['summary']['external_ai_calls'] == 0)
        check(key + '/stop_before_call', lambda p=p: p['summary']['send'] == 'PASS' or len(p['receiver_calls']) == 0)
        check(key + '/not_run_not_pass', lambda s=s: s['send'] == 'PASS' or s['answer'] == NOT_RUN and s['output'] == NOT_RUN)
        response, same_record = bridge.invoke({'inputs': {'scenario': key}})
        check(key + '/protocol_shape', lambda response=response: set(response) == {'outputs'} and type(response['outputs']) is str)
        normal_text = records['normal']['payload']['summary']['answer_text']
        check(key + '/no_blocked_body', lambda s=s, response=response: s['supplied'] or normal_text not in response['outputs'])
        for mutation in ('decision', 'wire', 'drop_event', 'event_result', 'state', 'scope'):
            forged = copy.deepcopy(record)
            q = forged['payload']
            if mutation == 'decision': q['summary']['decision'] = 'REJECT' if s['decision'] == 'PASS' else 'PASS'
            elif mutation == 'wire': q['wire']['applicant']['employees'] = 999
            elif mutation == 'drop_event': q['events'].pop(0)
            elif mutation == 'event_result': q['events'][0]['body']['data']['result']['decision'] = 'PASS' if q['events'][0]['body']['data']['result']['decision'] != 'PASS' else 'REJECT'
            elif mutation == 'state': q['ledger']['pending'] = not q['ledger']['pending']
            else: q['scope']['government_endorsement'] = True
            # Rehash the entire changed chain: rejection must not rely on stale hashes alone.
            previous = digest({'profile': PROFILE_HASH, 'scenario': key})
            for index, ev in enumerate(q['events']):
                ev['body']['sequence'] = index + 1
                ev['body']['previous'] = previous
                previous = digest(ev['body'])
                ev['sha256'] = previous
            forged['sha256'] = digest(q)
            check(key + '/rehash_attack/' + mutation, lambda f=forged: rejected(lambda: bridge.verify(f)))
    for key in ('unknown_delivery', 'unknown_after_retry'):
        s = records[key]['payload']['summary']
        check(key + '/consumption_retained', lambda s=s: s['used_units'] == 4 and s['pending'] and s['local_receiver_calls'] == 1 and not s['supplied'])
    check('duplicate/no_second_call', lambda: records['duplicate']['payload']['summary']['local_receiver_calls'] == 1)
    for key in ('copy_left', 'closed', 'stale_certificate'):
        check(key + '/no_post_end_supply', lambda key=key: not records[key]['payload']['summary']['supplied'])
    check('closed/certificate_is_not_read_permission', lambda: records['closed']['payload']['summary']['termination_confirmed'] and not records['closed']['payload']['summary']['supplied'])
    check('model_policy_not_trusted', lambda: records['model_relaxes']['payload']['summary']['decision'] == 'REJECT')
    check('approved_change_keeps_other_origin', lambda: records['approved_secondary']['payload']['summary']['observation']['origins_bound'])
    # Alter the stored, accepted text and recompute all outer hashes.
    forged = copy.deepcopy(records['normal'])
    forged['payload']['lifecycle_state']['objects']['S']['text'] = 'unrelated answer'
    forged['sha256'] = digest(forged['payload'])
    check('different_managed_answer', lambda: rejected(lambda: bridge.verify(forged)))
    invalid_json = ['{"a":1,"a":2}', '{"x":NaN}', '{"x":Infinity}', '{"x":-Infinity}', '{',
                    '{"inputs":{"scenario":"normal","scenario":"closed"}}', '{"x":9007199254740992}']
    for index, text in enumerate(invalid_json):
        check('json/' + str(index), lambda text=text: rejected(lambda: parse_json(text)))
    invalid_requests = [{}, [], None, {'inputs': None}, {'inputs': {'scenario': True}},
                        {'inputs': {'scenario': 1}}, {'inputs': {'scenario': 'unknown'}},
                        {'inputs': {'scenario': 'normal', 'policy': {'allow': True}}},
                        {'inputs': {'scenario': 'normal'}, 'outputs': 'PASS'},
                        {'inputs': {'scenario': '../cases.json'}}, {'inputs': {'scenario': ['normal']}}]
    for index, body in enumerate(invalid_requests):
        check('api/schema/' + str(index), lambda body=body: rejected(lambda: bridge.invoke(body)))
    collection = bridge.all_records()
    for mutation in ('drop', 'duplicate', 'reorder', 'source'):
        changed = copy.deepcopy(collection)
        if mutation == 'drop': changed['records'].pop()
        elif mutation == 'duplicate': changed['records'].append(changed['records'][0])
        elif mutation == 'reorder': changed['records'].reverse()
        else: changed['source_binding']['version'] = 'forged'
        check('collection/' + mutation, lambda changed=changed: rejected(lambda: bridge.verify_document(changed)))
    count = 0
    for observation in all_composition_inputs():
        actual = compose(observation)
        prerequisite = all(observation[k] == 'PASS' for k in ('send', 'output', 'answer'))
        identity = all(observation[k] for k in ('same_request', 'same_answer', 'origins_bound'))
        expected = {'may_register': prerequisite and identity,
                    'may_supply': prerequisite and identity and observation['registered'] and observation['use'] == 'PASS' and observation['action_ok']}
        require(actual == expected, 'Independent finite composition oracle mismatch')
        count += 1
    check('composition/exhaustive_8192', lambda: count == 8192)
    for name, lock in bridge.cfg['upstream_files'].items():
        check('unchanged_source/' + name, lambda name=name, lock=lock: filehash(ROOT / name) == lock['sha256'])
    failures = [r for r in rows if not r['passed']]
    return {'schema': 'gennai-civic-bridge-tests/1.0', 'total': len(rows),
            'passed': len(rows) - len(failures), 'upstream': upstream,
            'composition_inputs': count, 'failures': failures}


def make_server(bridge: Bridge, port: int = 0, key: str | None = None, capture_dir: Path | None = None) -> ThreadingHTTPServer:
    token = key or secrets.token_urlsafe(32)
    require(type(token) is str and 24 <= len(token) <= 256, 'API key must be 24–256 characters')
    class Handler(BaseHTTPRequestHandler):
        protocol_version = 'HTTP/1.0'
        server_version = 'CivicAssuranceReference/1.0'
        def setup(self):
            super().setup()
            self.connection.settimeout(5)
        def log_message(self, *args):
            pass  # Do not log payloads, authorization headers, or private keys.
        def respond(self, code, value, content_type='application/json; charset=utf-8'):
            raw = value.encode('utf-8') if type(value) is str else canonical(value).encode('utf-8')
            self.send_response(code)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(len(raw)))
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Content-Security-Policy', "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; connect-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'")
            self.end_headers()
            self.wfile.write(raw)
        def trusted_origin(self):
            host = self.headers.get('Host', '')
            allowed = {f'127.0.0.1:{self.server.server_port}', f'localhost:{self.server.server_port}'}
            origin = self.headers.get('Origin')
            return host in allowed and (origin is None or origin == 'http://' + host)
        def do_GET(self):
            if not self.trusted_origin():
                self.respond(403, {'error': 'Host or Origin is not permitted'}); return
            if self.path == '/health':
                self.respond(200, {'status': 'ok', 'mode': 'synthetic-reference', 'external_ai_calls': 0}); return
            if self.path == '/registration.json':
                self.respond(200, bridge.registration()); return
            if self.path == '/README.md':
                self.respond(200, (ROOT / 'README.md').read_text(encoding='utf-8'), 'text/plain; charset=utf-8'); return
            if self.path in ('/', '/demo.html'):
                page = (ROOT / 'demo.html').read_text(encoding='utf-8')
                runtime = canonical({'mode': 'live-local', 'api_key': token})
                page = re.sub(r'(<script id="runtime" type="application/json">).*?(</script>)',
                              lambda match: match.group(1) + runtime + match.group(2), page, flags=re.S)
                self.respond(200, page, 'text/html; charset=utf-8'); return
            self.respond(404, {'error': 'Not found'})
        def do_POST(self):
            if not self.trusted_origin():
                self.respond(403, {'error': 'Host or Origin is not permitted'}); return
            supplied = self.headers.get('x-api-key', '')
            if not hmac.compare_digest(supplied.encode('utf-8'), token.encode('utf-8')):
                self.respond(401, {'error': 'Invalid API key'}); return
            if self.path not in ('/invoke', '/demo-run'):
                self.respond(404, {'error': 'Not found'}); return
            if self.headers.get('Transfer-Encoding'):
                self.respond(400, {'error': 'Chunked bodies are not supported'}); return
            if self.headers.get_content_type() != 'application/json':
                self.respond(415, {'error': 'Content-Type must be application/json'}); return
            try:
                value = self.headers.get('Content-Length', '')
                require(value.isascii() and value.isdigit() and len(value) < 10, 'Content-Length required')
                size = int(value)
                if size > HTTP_MAX_BYTES:
                    self.respond(413, {'error': 'Body too large'}); return
                require(size > 0, 'Empty body')
                self.connection.settimeout(5)
                raw = self.rfile.read(size)
                require(len(raw) == size, 'Incomplete body')
                body = parse_json(raw.decode('utf-8'))
                output, record = bridge.invoke(body)
                if capture_dir is not None:
                    write_json(capture_dir / ('record-' + uuid.uuid4().hex + '.json'), record)
                self.respond(200, output if self.path == '/invoke' else {'response': output, 'record': record})
            except (InputError, ValueError, UnicodeError, KeyError, TypeError, TimeoutError):
                self.respond(400, {'error': 'Invalid or unsupported request; no successful decision is asserted'})
            except Exception:
                self.respond(500, {'error': 'Verification failed; no answer is released'})
    server = ThreadingHTTPServer(('127.0.0.1', port), Handler)
    server.bridge_token = token
    return server


def http_tests(bridge: Bridge) -> dict:
    server = make_server(bridge)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    root = 'http://127.0.0.1:' + str(server.server_port)
    rows = []
    def call(path='/invoke', value=None, raw=None, token=True, extra=None, method='POST'):
        payload = raw if raw is not None else canonical(value).encode('utf-8') if value is not None else b''
        headers = {'Content-Type': 'application/json'}
        if token: headers['x-api-key'] = server.bridge_token
        headers.update(extra or {})
        request = urllib.request.Request(root + path, data=payload if method == 'POST' else None, headers=headers, method=method)
        try:
            with urllib.request.urlopen(request, timeout=15) as result:
                return result.status, result.read(), result.headers
        except urllib.error.HTTPError as exc:
            return exc.code, exc.read(), exc.headers
    def check(name, success):
        rows.append({'name': name, 'passed': bool(success)})
    try:
        for key in bridge.scenarios:
            code, raw, headers = call(value={'inputs': {'scenario': key}})
            actual = parse_json(raw.decode('utf-8'))
            expected, _ = bridge.invoke({'inputs': {'scenario': key}})
            check('sync/' + key, code == 200 and actual == expected and set(actual) == {'outputs'})
        for name, args, expected in [
            ('unauthenticated', {'value': {'inputs': {'scenario': 'normal'}}, 'token': False}, 401),
            ('foreign-origin', {'value': {'inputs': {'scenario': 'normal'}}, 'extra': {'Origin': 'https://untrusted.invalid'}}, 403),
            ('foreign-host', {'value': {'inputs': {'scenario': 'normal'}}, 'extra': {'Host': 'untrusted.invalid'}}, 403),
            ('duplicate-keys', {'raw': b'{"inputs":{"scenario":"normal","scenario":"closed"}}'}, 400),
            ('nan', {'raw': b'{"inputs":{"scenario":NaN}}'}, 400),
            ('bad-utf8', {'raw': b'\xff'}, 400),
            ('unknown-scenario', {'value': {'inputs': {'scenario': 'unknown'}}}, 400),
            ('extra-fields', {'value': {'inputs': {'scenario': 'normal', 'force_pass': True}}}, 400),
            ('array-body', {'value': []}, 400),
            ('wrong-content-type', {'value': {'inputs': {'scenario': 'normal'}}, 'extra': {'Content-Type': 'text/plain'}}, 415),
            ('oversized', {'raw': b' ' * (HTTP_MAX_BYTES + 1)}, 413),
            ('unknown-route', {'path': '/unsafe', 'value': {'inputs': {'scenario': 'normal'}}}, 404),
            ('no-file-serving', {'path': '/poc.py', 'method': 'GET'}, 404),
            ('no-path-traversal', {'path': '/../cases.json', 'method': 'GET'}, 404),
        ]:
            code, _, _ = call(**args)
            check(name, code == expected)
        code, raw, _ = call('/registration.json', method='GET')
        check('registration', code == 200 and parse_json(raw.decode()) == bridge.registration())
        code, raw, _ = call('/README.md', method='GET')
        check('documentation', code == 200 and raw.decode('utf-8') == (ROOT / 'README.md').read_text(encoding='utf-8'))
        code, raw, _ = call('/demo-run', value={'inputs': {'scenario': 'normal'}})
        result = parse_json(raw.decode('utf-8'))
        check('demo-record-replay', code == 200 and bridge.verify(result['record'])['ok'])
    finally:
        server.shutdown(); server.server_close(); thread.join(timeout=5)
    failures = [r for r in rows if not r['passed']]
    return {'total': len(rows), 'passed': len(rows) - len(failures), 'failures': failures,
            'scope': 'real localhost HTTP, synthetic generator; no deployed Gennai OSS environment'}


def snapshot_rows(bridge: Bridge, evidence: dict) -> dict:
    rows = []
    for record in evidence['records']:
        p = record['payload']
        checks, timeline = [], []
        for event in p['events']:
            body = event['body']
            data = body['data']
            result = data.get('result', {})
            checks.extend(copy.deepcopy(result.get('checks', [])))
            timeline.append({'kind': body['kind'], 'operation': data.get('command', {}).get('op', ''),
                             'status': result.get('decision', result.get('status', ''))})
        rows.append({'key': p['scenario'], 'label': p['label'], 'summary': p['summary'],
                     'hash': record['sha256'], 'note': bridge.scenarios[p['scenario']]['note'],
                     'checks': checks, 'timeline': timeline})
    return {'records': rows}


def update_snapshot(bridge: Bridge, evidence: dict, path: Path) -> None:
    page = (ROOT / 'demo.html').read_text(encoding='utf-8')
    embedded = canonical(snapshot_rows(bridge, evidence)).replace('<', '\\u003c').replace('&', '\\u0026')
    page, count = re.subn(r'(<script id="snapshot" type="application/json">).*?(</script>)',
                         lambda match: match.group(1) + embedded + match.group(2), page, flags=re.S)
    require(count == 1, 'Snapshot slot not found')
    if path.resolve() != (ROOT / 'demo.html').resolve():
        try:
            readme_href = Path(os.path.relpath(ROOT / 'README.md', path.parent)).as_posix()
        except ValueError:
            readme_href = (ROOT / 'README.md').as_uri()
        page = page.replace('href="README.md"', 'href="' + html.escape(readme_href, quote=True) + '"')
    path.write_text(page, encoding='utf-8', newline='\n')


def verify_snapshot(bridge: Bridge, evidence: dict) -> bool:
    page = (ROOT / 'demo.html').read_text(encoding='utf-8')
    found = re.search(r'<script id="snapshot" type="application/json">(.*?)</script>', page, re.S)
    require(found is not None, 'Missing browser snapshot')
    return parse_json(found.group(1)) == snapshot_rows(bridge, evidence)


def node_tests(bridge: Bridge) -> dict:
    require(shutil.which('node') is not None, 'Node.js required; test is NOT checked')
    page = (ROOT / 'demo.html').read_text(encoding='utf-8')
    match = re.search(r'<script id="gate-model">(.*?)</script>', page, re.S)
    require(match is not None, 'Missing independent browser composition model')
    inputs = list(all_composition_inputs())
    inputs += [bridge.run_case(key)['payload']['summary']['observation'] for key in bridge.scenarios]
    code = match.group(1) + "\nconst fs=require('fs');const rows=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(rows.map(composeModel)));\n"
    result = subprocess.run(['node', '-e', code], input=canonical(inputs), capture_output=True,
                            encoding='utf-8', timeout=45, check=True)
    actual = parse_json(result.stdout)
    expected = [compose(o) for o in inputs]
    require(actual == expected, 'Python/JavaScript composition mismatch')
    return {'inputs': len(inputs), 'matched': len(inputs), 'scope': 'composition model; not complete independent execution of all three upstream engines'}


def browser_tests(bridge: Bridge, screenshots: Path | None = None, snapshot_only: bool = False) -> dict:
    try:
        from playwright.sync_api import sync_playwright
    except ImportError as exc:
        raise InputError('Playwright is required for browser-test; not checked') from exc
    server = make_server(bridge)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    errors, checks = [], 0
    try:
        with sync_playwright() as playwright:
            executable = None if Path(playwright.chromium.executable_path).is_file() else shutil.which('chromium')
            browser = playwright.chromium.launch(headless=True, args=['--no-sandbox'], executable_path=executable)
            page = browser.new_page(viewport={'width': 1440, 'height': 1150}, device_scale_factor=1)
            page.on('pageerror', lambda error: errors.append(str(error)))
            if snapshot_only:
                page.set_content((ROOT / 'demo.html').read_text(encoding='utf-8'), wait_until='load')
            else:
                page.goto('http://127.0.0.1:' + str(server.server_port), wait_until='networkidle')
            from playwright.sync_api import expect
            for key, scene in bridge.scenarios.items():
                page.select_option('#scenario', key)
                expect(page.locator('#caseTitle')).to_have_text(scene['label'])
                expect(page.locator('#run')).to_be_enabled()
                require(not page.is_visible('#error'), 'Browser error shown: ' + key)
                require(page.inner_text('#decision') == scene['expected'], 'Wrong browser decision: ' + key)
                expected = bridge.run_case(key)['payload']['summary']
                require(page.is_visible('#answerText') == expected['supplied'], 'Browser released blocked answer: ' + key)
                if expected['supplied']:
                    require(page.inner_text('#answerText') == expected['answer_text'], 'Browser text differs from checked text')
                checks += 1
            page.select_option('#scenario', 'normal')
            expect(page.locator('#caseTitle')).to_have_text('必要項目だけで回答案を使う')
            expect(page.locator('#run')).to_be_enabled()
            if screenshots:
                screenshots.mkdir(parents=True, exist_ok=True)
                page.screenshot(path=str(screenshots / 'desktop.png'), full_page=True)
            for width in (390, 768, 1440):
                page.set_viewport_size({'width': width, 'height': 1050})
                # Full-page PNG width reflects scrollable content width without JavaScript eval.
                screenshot = page.screenshot(full_page=True)
                require(screenshot.startswith(b'\x89PNG\r\n\x1a\n'), 'Invalid browser screenshot')
                require(int.from_bytes(screenshot[16:20], 'big') <= width, 'Horizontal overflow at ' + str(width))
                checks += 1
                if screenshots and width == 390:
                    page.screenshot(path=str(screenshots / 'mobile.png'), full_page=True)
            # The file:// presentation is a saved-record viewer, not a simulated live run.
            offline = browser.new_page(viewport={'width': 1280, 'height': 1000})
            offline.on('pageerror', lambda error: errors.append(str(error)))
            offline.set_content((ROOT / 'demo.html').read_text(encoding='utf-8'), wait_until='load')
            offline.select_option('#scenario', 'closed')
            require(offline.inner_text('#mode') == '保存済み実行記録', 'Snapshot mislabeled as live')
            require(not offline.is_visible('#answerText') and offline.inner_text('#decision') == 'PASS', 'Termination snapshot leaked text')
            checks += 1
            require(not errors, 'Browser script error: ' + '; '.join(errors))
            browser.close()
    finally:
        server.shutdown(); server.server_close(); thread.join(timeout=5)
    return {'checks': checks, 'passed': checks, 'script_errors': errors,
            'mode': 'snapshot-only' if snapshot_only else 'live-local-and-snapshot',
            'live_bridge_ui_checked': not snapshot_only,
            'scope': 'our bridge display; not official Gennai OSS UI'}


def lean_observation(o: dict) -> str:
    fields = [('send', 'send'), ('output', 'output'), ('answer', 'answer'),
              ('sameRequest', 'same_request'), ('sameAnswer', 'same_answer'),
              ('originsBound', 'origins_bound'), ('registered', 'registered'),
              ('use', 'use'), ('actionOk', 'action_ok')]
    def value(v):
        return ('true' if v else 'false') if type(v) is bool else '.' + v
    return '({ ' + ', '.join(a + ' := ' + value(o[b]) for a, b in fields) + ' } : CivicBridge.Observation)'


def lean_checks(bridge: Bridge) -> dict:
    require(shutil.which('lake') is not None, 'Lean/Lake is not installed here. Formal checking NOT executed; no success is claimed.')
    require(shutil.which('lean') is not None, 'Lean is required')
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=ROOT, capture_output=True,
                             encoding='utf-8', check=True, timeout=90)
    require('4.19.0' in version.stdout, 'Use the fixed Lean 4.19.0 toolchain')
    build = subprocess.run(['lake', 'build'], cwd=ROOT, capture_output=True, encoding='utf-8', timeout=600)
    require(build.returncode == 0, 'Lean build failed:\n' + (build.stdout + build.stderr)[-20000:])
    audit = subprocess.run(['lake', 'env', 'lean', 'CivicBridge.lean'], cwd=ROOT, capture_output=True,
                           encoding='utf-8', timeout=180)
    require(audit.returncode == 0, 'Lean axiom audit failed:\n' + (audit.stdout + audit.stderr)[-20000:])
    log = audit.stdout + audit.stderr
    theorem_names = re.findall(r'^theorem\s+(\w+)', (ROOT / 'CivicBridge.lean').read_text(encoding='utf-8'), re.M)
    require(len(theorem_names) == 18 and all('CivicBridge.' + name in log for name in theorem_names),
            'Missing named-theorem dependency reports')
    require(not any(word in log for word in ('sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler')), 'Untrusted proof dependency')
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log, re.S):
        names = {v.strip() for v in group.split(',') if v.strip()}
        require(names <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom dependencies: ' + str(names))
    observations = list(all_composition_inputs())
    observations += [bridge.run_case(key)['payload']['summary']['observation'] for key in bridge.scenarios]
    with tempfile.TemporaryDirectory(prefix='civic-bridge-lean-') as directory:
        for offset in range(0, len(observations), 256):
            lines = ['import CivicBridge', 'set_option autoImplicit false', 'set_option warningAsError true']
            for obs in observations[offset:offset + 256]:
                expected = compose(obs)
                reg = 'true' if expected['may_register'] else 'false'
                supply = 'true' if expected['may_supply'] else 'false'
                value = lean_observation(obs)
                lines.append(f'example : CivicBridge.mayRegister {value} = {reg} := by decide')
                lines.append(f'example : CivicBridge.maySupply {value} = {supply} := by decide')
            path = Path(directory) / 'Concrete.lean'
            path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                    capture_output=True, encoding='utf-8', timeout=180)
            require(result.returncode == 0, 'Lean concrete-input check failed:\n' + (result.stdout + result.stderr)[-12000:])
    return {'lean_checked': True, 'version': '4.19.0', 'integration_theorems': len(theorem_names),
            'concrete_inputs': len(observations), 'upstream_models': 'built unchanged', 'axiom_audit': 'passed'}


def assert_success(report: dict, kind: str):
    if 'passed' in report:
        total = report.get('total', report.get('checks'))
        require(report['passed'] == total and not report.get('failures'), kind + ' failed: ' + canonical(report))


def cli() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command')
    run = sub.add_parser('run', help='Run all fixed synthetic scenarios')
    run.add_argument('--case', choices=[s['key'] for s in config()['scenarios']])
    run.add_argument('--out', type=Path, default=ROOT / 'output')
    for command in ('prepare', 'test', 'http-test', 'node-test', 'lean-test', 'publish'):
        sub.add_parser(command)
    verify = sub.add_parser('verify'); verify.add_argument('path', type=Path)
    browser = sub.add_parser('browser-test'); browser.add_argument('--screenshots', type=Path)
    browser.add_argument('--snapshot-only', action='store_true', help='Render saved records without browser network access; explicitly excludes live UI integration')
    ci = sub.add_parser('ci'); ci.add_argument('--snapshot-only', action='store_true', help='Only allowed with --runtime-only')
    ci.add_argument('--runtime-only', action='store_true', help='Explicitly exclude Lean; never marks formal checks as successful')
    serve = sub.add_parser('serve'); serve.add_argument('--port', type=int, default=8765)
    args = parser.parse_args()
    command = args.command or 'run'
    bridge = Bridge()
    if command == 'prepare':
        print('Locked original sources are ready. No existing repository or experiment record was changed.')
        return 0
    if command == 'test':
        report = run_tests(bridge); print(json.dumps(report, ensure_ascii=False, indent=2)); assert_success(report, 'Python tests'); return 0
    if command == 'http-test':
        report = http_tests(bridge); print(json.dumps(report, ensure_ascii=False, indent=2)); assert_success(report, 'HTTP tests'); return 0
    if command == 'node-test':
        print(json.dumps(node_tests(bridge), ensure_ascii=False, indent=2)); return 0
    if command == 'browser-test':
        print(json.dumps(browser_tests(bridge, args.screenshots, args.snapshot_only), ensure_ascii=False, indent=2)); return 0
    if command == 'lean-test':
        print(json.dumps(lean_checks(bridge), ensure_ascii=False, indent=2)); return 0
    if command == 'verify':
        count = bridge.verify_document(read_json(args.path)); print(f'Replayed {count} record(s). HOLD/REJECT remain HOLD/REJECT; not issuer authentication.'); return 0
    if command == 'publish':
        tests = run_tests(bridge); assert_success(tests, 'Python tests')
        http = http_tests(bridge); assert_success(http, 'HTTP tests')
        evidence = bridge.all_records(); require(bridge.verify_document(evidence) == len(bridge.scenarios), 'Replay failed')
        write_json(ROOT / 'evidence.json', evidence)
        update_snapshot(bridge, evidence, ROOT / 'demo.html')
        require(verify_snapshot(bridge, evidence), 'Snapshot mismatch')
        print(json.dumps({'published_locally': True, 'records': len(bridge.scenarios),
                          'python': tests, 'http': http, 'lean_checked_by_this_command': False,
                          'external_uploads': 0}, ensure_ascii=False, indent=2))
        return 0
    if command == 'ci':
        tests = run_tests(bridge); assert_success(tests, 'Python tests')
        http = http_tests(bridge); assert_success(http, 'HTTP tests')
        node = node_tests(bridge)
        evidence = read_json(ROOT / 'evidence.json')
        count = bridge.verify_document(evidence)
        require(verify_snapshot(bridge, evidence), 'Published snapshot differs from replayed evidence')
        require(not args.snapshot_only or args.runtime_only, '--snapshot-only is only valid with --runtime-only; full CI cannot skip the live UI test')
        browser = browser_tests(bridge, snapshot_only=args.snapshot_only)
        result = {'python': tests, 'http': http, 'javascript': node, 'browser': browser, 'replayed_records': count,
                  'gennai_oss_environment_tested': False, 'external_ai_calls': 0}
        if args.runtime_only:
            result.update(runtime_ok=True, lean_checked=False, validation_scope='runtime-only; formal checks not executed')
        else:
            result['formal'] = lean_checks(bridge)
            result.update(runtime_ok=True, lean_checked=True, validation_scope='synthetic-reference-model-and-runtime')
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    if command == 'serve':
        require(1 <= args.port <= 65535, 'Invalid port')
        capture = ROOT / 'output' / ('http-' + uuid.uuid4().hex[:12])
        server = make_server(bridge, args.port, os.environ.get('CIVIC_BRIDGE_API_KEY'), capture)
        print(f'Open http://127.0.0.1:{server.server_port}/  (Ctrl+C to stop)', flush=True)
        print('Synthetic reference only. Bound to localhost; no external AI calls.', flush=True)
        if not os.environ.get('CIVIC_BRIDGE_API_KEY'):
            print('A temporary local demo key was generated. For API clients, set CIVIC_BRIDGE_API_KEY before starting.', flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            server.server_close()
        return 0
    out_root = getattr(args, 'out', ROOT / 'output')
    folder = out_root / ('run-' + uuid.uuid4().hex[:12])
    key = getattr(args, 'case', None)
    evidence = bridge.run_case(key) if key else bridge.all_records()
    count = bridge.verify_document(evidence)
    write_json(folder / 'evidence.json', evidence)
    write_json(folder / 'registration.json', bridge.registration())
    view = evidence if 'records' in evidence else {'records': [evidence]}
    update_snapshot(bridge, view, folder / 'report.html')
    for record in view['records']:
        print(f"{record['payload']['summary']['decision']:6} {record['payload']['label']}")
    print(f'\nReplayed {count} record(s). Open: {folder / "report.html"}')
    print('No external AI / no deployed Gennai OSS test / no government certification.')
    return 0


if __name__ == '__main__':
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='replace')
    try:
        raise SystemExit(cli())
    except Exception as exc:
        print('検査・実行は完了していません。成功として扱わないでください。\n' + str(exc), file=sys.stderr)
        raise SystemExit(2)
