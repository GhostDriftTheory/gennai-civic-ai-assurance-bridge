import Std

/-!
# 自治体AI・プライバシーアシュアランス：公開用の判定・状態遷移モデル
Copyright © 2026 AI Assurance, Inc. All rights reserved. 利用条件はREADME.md。

固定の合成資料から得る観測値を入力に、8つの送信条件、4つの出力条件、
累積点数の上限、未確定時の消費保持、重複要求、出力採用を形式化する。
真偽値は原子的な照合の観測境界であり、Pythonの判定結果を入力にはしない。
additional は同じ固定対象・固定資料の新規項目集合から求めるデモ点数。
点数は差分プライバシーのεでも再識別確率でもない。

モデルの定理は型の全入力に対するもの。Python/JavaScriptとの具体的照合は
`python poc.py ci` で別途実施。Python全体の意味的同値性、原文分類、暗号、
JSON解析、ファイルI/O、実際の外部システムや法令の適合性を証明していない。
公開用の単一対象・逐次処理モデルであり、商用の分散台帳や汎用開示推定を含まない。
-/
set_option autoImplicit false
set_option warningAsError true
namespace CivicPrivacyAssurance

inductive Status where
  | PASS | HOLD | REJECT
  deriving DecidableEq, Repr

def referenceSHA256 : String :=
  "7ad18cd83dc87acbca7ca0895d64e74b68b1c7e4df461e0800c8e301571aeda7"

def worst (xs : List Status) : Status :=
  if Status.REJECT ∈ xs then .REJECT
  else if Status.HOLD ∈ xs then .HOLD
  else .PASS

theorem worst_reject_iff (xs : List Status) :
    worst xs = .REJECT ↔ Status.REJECT ∈ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_hold_iff (xs : List Status) :
    worst xs = .HOLD ↔ Status.REJECT ∉ xs ∧ Status.HOLD ∈ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_pass_iff_no_blockers (xs : List Status) :
    worst xs = .PASS ↔ Status.REJECT ∉ xs ∧ Status.HOLD ∉ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_pass_iff (xs : List Status) :
    worst xs = .PASS ↔ ∀ s ∈ xs, s = Status.PASS := by
  constructor
  · intro h s hs
    have hn := (worst_pass_iff_no_blockers xs).mp h
    cases s with
    | PASS => rfl
    | HOLD => exact False.elim (hn.2 hs)
    | REJECT => exact False.elim (hn.1 hs)
  · intro h
    apply (worst_pass_iff_no_blockers xs).mpr
    constructor
    · intro hm
      have bad := h Status.REJECT hm
      cases bad
    · intro hm
      have bad := h Status.HOLD hm
      cases bad

theorem adding_checks_cannot_remove_reject (xs ys : List Status)
    (h : worst xs = .REJECT) : worst (xs ++ ys) = .REJECT := by
  apply (worst_reject_iff (xs ++ ys)).mpr
  exact List.mem_append.mpr (Or.inl ((worst_reject_iff xs).mp h))

def checked (b : Bool) : Status := if b then .PASS else .REJECT

theorem checked_pass_iff (b : Bool) : checked b = .PASS ↔ b = true := by
  cases b <;> decide

def supported (known ok : Bool) : Status :=
  if known then checked ok else .HOLD

theorem supported_pass_iff (known ok : Bool) :
    supported known ok = .PASS ↔ known = true ∧ ok = true := by
  cases known <;> cases ok <;> decide

theorem unknown_evidence_is_held (ok : Bool) : supported false ok = .HOLD := by
  rfl

def budgetCheck (known : Bool) (used additional limit : Nat) : Status :=
  supported known (decide (used + additional ≤ limit))

theorem budget_pass_iff (known : Bool) (used additional limit : Nat) :
    budgetCheck known used additional limit = .PASS ↔
      known = true ∧ used + additional ≤ limit := by
  simp [budgetCheck, supported_pass_iff]

def stateCheck (pending duplicate : Bool) : Status :=
  if duplicate then .REJECT else if pending then .HOLD else .PASS

theorem state_pass_iff (pending duplicate : Bool) :
    stateCheck pending duplicate = .PASS ↔ pending = false ∧ duplicate = false := by
  cases pending <;> cases duplicate <;> decide

structure Input where
  sourceOK : Bool
  scopeOK : Bool
  authorityKnown : Bool
  authorityOK : Bool
  termsKnown : Bool
  recipientOK : Bool
  termsOK : Bool
  fieldsOK : Bool
  evidenceKnown : Bool
  payloadOK : Bool
  ledgerKnown : Bool
  pending : Bool
  duplicate : Bool
  used : Nat
  additional : Nat
  limit : Nat
  deriving DecidableEq, Repr

def recipientCheck (x : Input) : Status :=
  worst [checked x.recipientOK, supported x.termsKnown x.termsOK]

def checks (x : Input) : List Status :=
  [checked x.sourceOK, checked x.scopeOK,
    supported x.authorityKnown x.authorityOK, recipientCheck x,
    checked x.fieldsOK, supported x.evidenceKnown x.payloadOK,
    budgetCheck x.ledgerKnown x.used x.additional x.limit,
    stateCheck x.pending x.duplicate]

def decision (x : Input) : Status := worst (checks x)

theorem exactly_eight_checks (x : Input) : (checks x).length = 8 := by rfl

theorem send_iff_all_checks_pass (x : Input) :
    decision x = .PASS ↔ ∀ s ∈ checks x, s = Status.PASS :=
  worst_pass_iff (checks x)

theorem pass_requires_check (x : Input) (s : Status)
    (h : decision x = .PASS) (hm : s ∈ checks x) : s = .PASS :=
  (send_iff_all_checks_pass x).mp h s hm

theorem reject_has_priority (x : Input) (h : Status.REJECT ∈ checks x) :
    decision x = .REJECT := (worst_reject_iff (checks x)).mpr h

theorem pass_requires_source (x : Input) (h : decision x = .PASS) : x.sourceOK = true := by
  apply (checked_pass_iff x.sourceOK).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_scope (x : Input) (h : decision x = .PASS) : x.scopeOK = true := by
  apply (checked_pass_iff x.scopeOK).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_authority (x : Input) (h : decision x = .PASS) :
    x.authorityKnown = true ∧ x.authorityOK = true := by
  apply (supported_pass_iff x.authorityKnown x.authorityOK).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_recipient (x : Input) (h : decision x = .PASS) :
    x.recipientOK = true := by
  have hc : recipientCheck x = .PASS := pass_requires_check x _ h (by simp [checks])
  apply (checked_pass_iff x.recipientOK).mp
  exact (worst_pass_iff _).mp hc (checked x.recipientOK) (by simp)

theorem pass_requires_terms (x : Input) (h : decision x = .PASS) :
    x.termsKnown = true ∧ x.termsOK = true := by
  have hc : recipientCheck x = .PASS := pass_requires_check x _ h (by simp [checks])
  apply (supported_pass_iff x.termsKnown x.termsOK).mp
  exact (worst_pass_iff _).mp hc (supported x.termsKnown x.termsOK) (by simp)

theorem pass_requires_allowed_fields (x : Input) (h : decision x = .PASS) :
    x.fieldsOK = true := by
  apply (checked_pass_iff x.fieldsOK).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_payload_binding (x : Input) (h : decision x = .PASS) :
    x.evidenceKnown = true ∧ x.payloadOK = true := by
  apply (supported_pass_iff x.evidenceKnown x.payloadOK).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_budget (x : Input) (h : decision x = .PASS) :
    x.ledgerKnown = true ∧ x.used + x.additional ≤ x.limit := by
  apply (budget_pass_iff x.ledgerKnown x.used x.additional x.limit).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_clear_state (x : Input) (h : decision x = .PASS) :
    x.pending = false ∧ x.duplicate = false := by
  apply (state_pass_iff x.pending x.duplicate).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem missing_authority_blocks (x : Input) (hm : x.authorityKnown = false) :
    decision x ≠ .PASS := by
  intro h
  have good := (pass_requires_authority x h).1
  simp [hm] at good

theorem unknown_history_blocks (x : Input) (hm : x.ledgerKnown = false) :
    decision x ≠ .PASS := by
  intro h
  have good := (pass_requires_budget x h).1
  simp [hm] at good

theorem pending_outcome_blocks (x : Input) (hm : x.pending = true) :
    decision x ≠ .PASS := by
  intro h
  have good := (pass_requires_clear_state x h).1
  simp [hm] at good

theorem duplicate_request_rejects (x : Input) (hd : x.duplicate = true) :
    decision x = .REJECT := by
  apply reject_has_priority x
  simp [checks, stateCheck, hd]

theorem forbidden_field_rejects (x : Input) (hf : x.fieldsOK = false) :
    decision x = .REJECT := by
  apply reject_has_priority x
  simp [checks, checked, hf]

theorem budget_excess_blocks (x : Input) (hb : x.limit < x.used + x.additional) :
    decision x ≠ .PASS := by
  intro h
  have bound := (pass_requires_budget x h).2
  omega

/-- 消費は送信許可時に進める。結果不明・出力不採用を理由に戻さない。 -/
def afterUnits (x : Input) : Nat :=
  if decision x = .PASS then x.used + x.additional else x.used

def pendingAfter (x : Input) (acknowledged : Bool) : Bool :=
  if decision x = .PASS then !acknowledged else x.pending

theorem blocked_send_preserves_units (x : Input) (h : decision x ≠ .PASS) :
    afterUnits x = x.used := by simp [afterUnits, h]

theorem allowed_send_charges_units (x : Input) (h : decision x = .PASS) :
    afterUnits x = x.used + x.additional := by simp [afterUnits, h]

theorem units_never_decrease (x : Input) : x.used ≤ afterUnits x := by
  by_cases h : decision x = .PASS
  · rw [allowed_send_charges_units x h]
    omega
  · simp [afterUnits, h]

theorem allowed_send_respects_limit (x : Input) (h : decision x = .PASS) :
    afterUnits x ≤ x.limit := by
  rw [allowed_send_charges_units x h]
  exact (pass_requires_budget x h).2

theorem blocked_send_preserves_pending (x : Input) (ack : Bool) (h : decision x ≠ .PASS) :
    pendingAfter x ack = x.pending := by simp [pendingAfter, h]

theorem unknown_outcome_retains_charge (x : Input) (h : decision x = .PASS) :
    afterUnits x = x.used + x.additional ∧ pendingAfter x false = true := by
  simp [afterUnits, pendingAfter, h]

theorem acknowledged_send_clears_pending (x : Input) (h : decision x = .PASS) :
    pendingAfter x true = false := by simp [pendingAfter, h]

structure OutputObservation where
  available : Bool
  acknowledged : Bool
  bindingKnown : Bool
  bindingOK : Bool
  fieldsOK : Bool
  textOK : Bool
  useOK : Bool
  deriving DecidableEq, Repr

def outputChecks (o : OutputObservation) : List Status :=
  [supported o.bindingKnown o.bindingOK, checked o.fieldsOK,
    checked o.textOK, checked o.useOK]

def adoption (x : Input) (o : OutputObservation) : Status :=
  if decision x = .PASS then
    if o.available && o.acknowledged then worst (outputChecks o) else .HOLD
  else .HOLD

theorem exactly_four_output_checks (o : OutputObservation) :
    (outputChecks o).length = 4 := by rfl

theorem adoption_pass_iff (x : Input) (o : OutputObservation) :
    adoption x o = .PASS ↔ decision x = .PASS ∧ o.available = true ∧
      o.acknowledged = true ∧ ∀ s ∈ outputChecks o, s = Status.PASS := by
  by_cases hd : decision x = .PASS <;>
    cases ha : o.available <;> cases hk : o.acknowledged <;>
      simp [adoption, hd, ha, hk, worst_pass_iff]

theorem adoption_requires_sent_request (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : decision x = .PASS :=
  ((adoption_pass_iff x o).mp h).1

theorem adoption_requires_acknowledgement (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : o.available = true ∧ o.acknowledged = true :=
  ⟨((adoption_pass_iff x o).mp h).2.1, ((adoption_pass_iff x o).mp h).2.2.1⟩

theorem adoption_requires_check (x : Input) (o : OutputObservation) (s : Status)
    (h : adoption x o = .PASS) (hm : s ∈ outputChecks o) : s = .PASS :=
  ((adoption_pass_iff x o).mp h).2.2.2 s hm

theorem adoption_requires_binding (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : o.bindingKnown = true ∧ o.bindingOK = true := by
  apply (supported_pass_iff o.bindingKnown o.bindingOK).mp
  exact adoption_requires_check x o _ h (by simp [outputChecks])

theorem adoption_requires_allowed_output (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : o.fieldsOK = true := by
  apply (checked_pass_iff o.fieldsOK).mp
  exact adoption_requires_check x o _ h (by simp [outputChecks])

theorem adoption_requires_text_match (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : o.textOK = true := by
  apply (checked_pass_iff o.textOK).mp
  exact adoption_requires_check x o _ h (by simp [outputChecks])

theorem adoption_requires_staff_only_use (x : Input) (o : OutputObservation)
    (h : adoption x o = .PASS) : o.useOK = true := by
  apply (checked_pass_iff o.useOK).mp
  exact adoption_requires_check x o _ h (by simp [outputChecks])

theorem unacknowledged_response_not_adopted (x : Input) (o : OutputObservation)
    (hk : o.acknowledged = false) : adoption x o ≠ .PASS := by
  intro h
  have good := (adoption_requires_acknowledgement x o h).2
  simp [hk] at good

theorem leaking_text_not_adopted (x : Input) (o : OutputObservation)
    (ht : o.textOK = false) : adoption x o ≠ .PASS := by
  intro h
  have good := adoption_requires_text_match x o h
  simp [ht] at good

inductive Action where
  | none | localMock | staffDraft | realNetwork | administrativeAward
  deriving DecidableEq, Repr

def sendAction (s : Status) : Action := if s = .PASS then .localMock else .none

def adoptAction (s : Status) : Action := if s = .PASS then .staffDraft else .none

theorem only_pass_calls_mock (s : Status) :
    sendAction s = .localMock ↔ s = .PASS := by cases s <;> decide

theorem only_pass_releases_draft (s : Status) :
    adoptAction s = .staffDraft ↔ s = .PASS := by cases s <;> decide

theorem model_never_authorizes_real_network (s : Status) :
    sendAction s ≠ .realNetwork := by cases s <;> decide

theorem model_never_authorizes_administrative_award (s : Status) :
    adoptAction s ≠ .administrativeAward := by cases s <;> decide

structure RecordView where
  evidenceOK : Bool
  recordedSend : Status
  recordedAdoption : Status
  recordedUnits : Nat
  recordedPending : Bool
  deriving DecidableEq, Repr

def reverify (x : Input) (o : OutputObservation) (r : RecordView) : Bool :=
  decide (r.evidenceOK = true ∧ r.recordedSend = decision x ∧
    r.recordedAdoption = adoption x o ∧ r.recordedUnits = afterUnits x ∧
    r.recordedPending = pendingAfter x o.acknowledged)

theorem reverify_preserves_send (x : Input) (o : OutputObservation) (r : RecordView)
    (h : reverify x o r = true) : r.recordedSend = decision x :=
  (of_decide_eq_true h).2.1

theorem reverify_preserves_adoption (x : Input) (o : OutputObservation) (r : RecordView)
    (h : reverify x o r = true) : r.recordedAdoption = adoption x o :=
  (of_decide_eq_true h).2.2.1

theorem reverify_preserves_units (x : Input) (o : OutputObservation) (r : RecordView)
    (h : reverify x o r = true) : r.recordedUnits = afterUnits x :=
  (of_decide_eq_true h).2.2.2.1

theorem changed_send_fails_reverification (x : Input) (o : OutputObservation) (r : RecordView)
    (hn : r.recordedSend ≠ decision x) : reverify x o r = false := by
  cases hv : reverify x o r with
  | false => rfl
  | true => exact False.elim (hn (reverify_preserves_send x o r hv))

end CivicPrivacyAssurance
