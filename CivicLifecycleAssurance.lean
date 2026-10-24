import Std

/-!
# PoC 3 — 派生情報の条件承継・管理範囲の利用終了
Copyright © 2026 AI Assurance, Inc. All rights reserved. 利用条件はREADME.md。

公開用の固定参照実装に対応する純粋なモデル。管理範囲の完全性、証拠の真正性、
内容・版の一致、権限の照合は観測境界。Python/JavaScriptの判定結果そのものを
入力する代わりに、元の管理状態からこれらの観測値を生成して照合する。
定理はモデルの型で表された全入力に対するもの。Python全体、JSON、SHA-256、
ファイルI/O、認証、物理消去、API提供者内部の削除の形式証明ではない。
利用終了の範囲は管理ゲート経由の業務利用。監査保持は別に明示する。
有限の具体例の照合と定理の証明検査は `python poc.py ci` で実行する。
-/
set_option autoImplicit false
set_option warningAsError true
namespace CivicLifecycleAssurance

inductive Status where
  | PASS | HOLD | REJECT
  deriving DecidableEq, Repr

def referenceSHA256 : String :=
  "e385c4c4379207b92355a2621f14422e4337e20fe4b2c7ba6f2407245f5a0add"

def worst (xs : List Status) : Status :=
  if Status.REJECT ∈ xs then .REJECT
  else if Status.HOLD ∈ xs then .HOLD else .PASS

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

def supported (known ok : Bool) : Status := if known then checked ok else .HOLD

theorem checked_pass_iff (b : Bool) : checked b = .PASS ↔ b = true := by
  cases b <;> decide

theorem supported_pass_iff (known ok : Bool) :
    supported known ok = .PASS ↔ known = true ∧ ok = true := by
  cases known <;> cases ok <;> decide

theorem unknown_evidence_is_held (ok : Bool) : supported false ok = .HOLD := by rfl

/-- 不明・競合は「存在し得る」。利用許可には確定した成立が必要。 -/
inductive Truth where
  | no | yes | unknown | conflict
  deriving DecidableEq, Repr

def may (t : Truth) : Bool := match t with
  | .no => false
  | _ => true

def sure (t : Truth) : Bool := match t with
  | .yes => true
  | _ => false

structure PathView where
  enabled : Truth
  reader : Truth
  deriving DecidableEq, Repr

def certain (p : PathView) : Bool := sure p.enabled && sure p.reader

def possible (p : PathView) : Bool := may p.enabled && may p.reader

theorem certain_implies_possible (p : PathView) :
    certain p = true → possible p = true := by
  cases p with
  | mk a b => cases a <;> cases b <;> decide

theorem disabled_route_is_impossible (reader : Truth) :
    possible ⟨.no, reader⟩ = false := by cases reader <;> decide

theorem unknown_is_not_absent : possible ⟨.yes, .unknown⟩ = true := by decide

theorem conflict_is_not_absent : possible ⟨.yes, .conflict⟩ = true := by decide

def routeUse (ps : List PathView) : Status :=
  if ps.any certain then .PASS else if ps.any possible then .HOLD else .REJECT

theorem route_use_pass_iff (ps : List PathView) :
    routeUse ps = .PASS ↔ ps.any certain = true := by
  cases hc : ps.any certain <;> cases hp : ps.any possible <;> simp [routeUse, hc, hp]

theorem no_route_does_not_authorize_use : routeUse [] = .REJECT := by decide

def routeEnd (p : PathView) : Status :=
  if possible p then (if certain p then .REJECT else .HOLD) else .PASS

theorem route_end_pass_iff (p : PathView) :
    routeEnd p = .PASS ↔ possible p = false := by
  cases p with
  | mk a b => cases a <;> cases b <;> decide

theorem live_route_prevents_end (p : PathView) (h : certain p = true) :
    routeEnd p = .REJECT := by
  simp [routeEnd, h, certain_implies_possible p h]

theorem uncertain_route_holds_end : routeEnd ⟨.yes, .unknown⟩ = .HOLD := by decide

theorem one_closed_premise_blocks_route (reader : Truth) :
    routeEnd ⟨.no, reader⟩ = .PASS := by cases reader <;> decide

structure UseInput where
  present : Bool
  inventoryKnown : Bool
  inventoryOK : Bool
  authorityKnown : Bool
  authorityOK : Bool
  conditionsKnown : Bool
  purposeOK : Bool
  recipientOK : Bool
  deadlineOK : Bool
  active : Bool
  paths : List PathView
  deriving DecidableEq, Repr

def useChecks (x : UseInput) : List Status :=
  [checked x.present, supported x.inventoryKnown x.inventoryOK,
   supported x.authorityKnown x.authorityOK, supported x.conditionsKnown x.purposeOK,
   checked x.recipientOK, checked x.deadlineOK, checked x.active, routeUse x.paths]

def useDecision (x : UseInput) : Status := worst (useChecks x)

theorem exactly_eight_use_checks (x : UseInput) : (useChecks x).length = 8 := by rfl

theorem use_iff_all_checks (x : UseInput) :
    useDecision x = .PASS ↔ ∀ s ∈ useChecks x, s = Status.PASS :=
  worst_pass_iff (useChecks x)

theorem use_requires_check (x : UseInput) (s : Status)
    (h : useDecision x = .PASS) (hm : s ∈ useChecks x) : s = .PASS :=
  (use_iff_all_checks x).mp h s hm

theorem use_requires_authority (x : UseInput) (h : useDecision x = .PASS) :
    x.authorityKnown = true ∧ x.authorityOK = true := by
  apply (supported_pass_iff x.authorityKnown x.authorityOK).mp
  exact use_requires_check x _ h (by simp [useChecks])

theorem use_requires_purpose (x : UseInput) (h : useDecision x = .PASS) :
    x.conditionsKnown = true ∧ x.purposeOK = true := by
  apply (supported_pass_iff x.conditionsKnown x.purposeOK).mp
  exact use_requires_check x _ h (by simp [useChecks])

theorem use_requires_recipient (x : UseInput) (h : useDecision x = .PASS) :
    x.recipientOK = true := by
  apply (checked_pass_iff x.recipientOK).mp
  exact use_requires_check x _ h (by simp [useChecks])

theorem use_requires_deadline (x : UseInput) (h : useDecision x = .PASS) :
    x.deadlineOK = true := by
  apply (checked_pass_iff x.deadlineOK).mp
  exact use_requires_check x _ h (by simp [useChecks])

theorem frozen_origin_rejects_use (x : UseInput) (h : x.active = false) :
    useDecision x = .REJECT := by
  apply (worst_reject_iff (useChecks x)).mpr
  simp [useChecks, checked, h]

theorem forbidden_recipient_rejects (x : UseInput) (h : x.recipientOK = false) :
    useDecision x = .REJECT := by
  apply (worst_reject_iff (useChecks x)).mpr
  simp [useChecks, checked, h]

structure GrantInput where
  proofPresent : Bool
  authorityOK : Bool
  targetOK : Bool
  beforeOK : Bool
  contextOK : Bool
  timeOK : Bool
  unused : Bool
  deriving DecidableEq, Repr

def grantChecks (x : GrantInput) : List Status :=
  [supported x.proofPresent x.authorityOK, supported x.proofPresent x.targetOK,
   supported x.proofPresent x.beforeOK, supported x.proofPresent x.contextOK,
   supported x.proofPresent x.timeOK, supported x.proofPresent x.unused]

def grantDecision (x : GrantInput) : Status := worst (grantChecks x)

theorem grant_requires_check (x : GrantInput) (s : Status)
    (h : grantDecision x = .PASS) (hm : s ∈ grantChecks x) : s = .PASS :=
  (worst_pass_iff (grantChecks x)).mp h s hm

theorem change_requires_bound_target (x : GrantInput) (h : grantDecision x = .PASS) :
    x.proofPresent = true ∧ x.targetOK = true := by
  apply (supported_pass_iff x.proofPresent x.targetOK).mp
  exact grant_requires_check x _ h (by simp [grantChecks])

theorem change_requires_before_state (x : GrantInput) (h : grantDecision x = .PASS) :
    x.proofPresent = true ∧ x.beforeOK = true := by
  apply (supported_pass_iff x.proofPresent x.beforeOK).mp
  exact grant_requires_check x _ h (by simp [grantChecks])

theorem change_requires_context (x : GrantInput) (h : grantDecision x = .PASS) :
    x.proofPresent = true ∧ x.contextOK = true := by
  apply (supported_pass_iff x.proofPresent x.contextOK).mp
  exact grant_requires_check x _ h (by simp [grantChecks])

theorem change_requires_valid_time (x : GrantInput) (h : grantDecision x = .PASS) :
    x.proofPresent = true ∧ x.timeOK = true := by
  apply (supported_pass_iff x.proofPresent x.timeOK).mp
  exact grant_requires_check x _ h (by simp [grantChecks])

theorem change_requires_unused_evidence (x : GrantInput) (h : grantDecision x = .PASS) :
    x.proofPresent = true ∧ x.unused = true := by
  apply (supported_pass_iff x.proofPresent x.unused).mp
  exact grant_requires_check x _ h (by simp [grantChecks])

theorem missing_evidence_cannot_relax (x : GrantInput) (hm : x.proofPresent = false) :
    grantDecision x ≠ .PASS := by
  intro h
  have good := (change_requires_bound_target x h).1
  simp [hm] at good

/-- Conditionの起源と種類を保持したまま、検証済みの要素だけを変更する。 -/
structure Condition where
  origin : Nat
  kind : Nat
  value : Nat
  deriving DecidableEq, Repr

def inheritConditions (left right : List Condition) (_supportKnown : Bool) : List Condition :=
  left ++ right

theorem left_conditions_inherited (left right : List Condition) (known : Bool)
    (c : Condition) (h : c ∈ left) : c ∈ inheritConditions left right known :=
  List.mem_append.mpr (Or.inl h)

theorem right_conditions_inherited (left right : List Condition) (known : Bool)
    (c : Condition) (h : c ∈ right) : c ∈ inheritConditions left right known :=
  List.mem_append.mpr (Or.inr h)

theorem unknown_support_does_not_drop_conditions (left right : List Condition) :
    inheritConditions left right false = left ++ right := by rfl

def amendOne (old target : Condition) (replacement : Nat) (g : GrantInput) : Condition :=
  if old = target ∧ grantDecision g = .PASS then { old with value := replacement } else old

def amendAll (xs : List Condition) (target : Condition) (replacement : Nat)
    (g : GrantInput) : List Condition := xs.map (fun c => amendOne c target replacement g)

theorem other_condition_unchanged (old target : Condition) (v : Nat) (g : GrantInput)
    (h : old ≠ target) : amendOne old target v g = old := by
  simp [amendOne, h]

theorem unverified_change_keeps_condition (old target : Condition) (v : Nat) (g : GrantInput)
    (h : grantDecision g ≠ .PASS) : amendOne old target v g = old := by
  simp [amendOne, h]

theorem verified_target_changes_only_value (target : Condition) (v : Nat) (g : GrantInput)
    (h : grantDecision g = .PASS) : amendOne target target v g = { target with value := v } := by
  simp [amendOne, h]

theorem amendment_preserves_origin (old target : Condition) (v : Nat) (g : GrantInput) :
    (amendOne old target v g).origin = old.origin := by
  unfold amendOne
  split <;> rfl

theorem amendment_preserves_kind (old target : Condition) (v : Nat) (g : GrantInput) :
    (amendOne old target v g).kind = old.kind := by
  unfold amendOne
  split <;> rfl

theorem amendment_keeps_all_elements (xs : List Condition) (target : Condition)
    (v : Nat) (g : GrantInput) : (amendAll xs target v g).length = xs.length := by
  simp [amendAll]

structure EndInput where
  inventoryKnown : Bool
  inventoryOK : Bool
  frozen : Bool
  paths : List PathView
  pending : Nat
  unknown : Nat
  closureKnown : Bool
  closureOK : Bool
  retainedBody : Bool
  auditException : Bool
  deriving DecidableEq, Repr

def endChecks (x : EndInput) : List Status :=
  [supported x.inventoryKnown x.inventoryOK, checked x.frozen,
   worst (x.paths.map routeEnd), supported (decide (x.pending = 0 ∧ x.unknown = 0)) true,
   supported x.closureKnown x.closureOK, checked (!x.retainedBody || x.auditException)]

def endDecision (x : EndInput) : Status := worst (endChecks x)

theorem exactly_six_end_checks (x : EndInput) : (endChecks x).length = 6 := by rfl

theorem end_iff_all_checks (x : EndInput) :
    endDecision x = .PASS ↔ ∀ s ∈ endChecks x, s = Status.PASS :=
  worst_pass_iff (endChecks x)

theorem end_requires_check (x : EndInput) (s : Status)
    (h : endDecision x = .PASS) (hm : s ∈ endChecks x) : s = .PASS :=
  (end_iff_all_checks x).mp h s hm

theorem end_requires_complete_inventory (x : EndInput) (h : endDecision x = .PASS) :
    x.inventoryKnown = true ∧ x.inventoryOK = true := by
  apply (supported_pass_iff x.inventoryKnown x.inventoryOK).mp
  exact end_requires_check x _ h (by simp [endChecks])

theorem end_requires_barrier (x : EndInput) (h : endDecision x = .PASS) :
    x.frozen = true := by
  apply (checked_pass_iff x.frozen).mp
  exact end_requires_check x _ h (by simp [endChecks])

theorem end_requires_closed_operations (x : EndInput) (h : endDecision x = .PASS) :
    x.pending = 0 ∧ x.unknown = 0 := by
  have hc : supported (decide (x.pending = 0 ∧ x.unknown = 0)) true = .PASS :=
    end_requires_check x _ h (by simp [endChecks])
  exact of_decide_eq_true ((supported_pass_iff _ _).mp hc).1

theorem end_requires_closure_evidence (x : EndInput) (h : endDecision x = .PASS) :
    x.closureKnown = true ∧ x.closureOK = true := by
  apply (supported_pass_iff x.closureKnown x.closureOK).mp
  exact end_requires_check x _ h (by simp [endChecks])

theorem end_requires_each_route_absent (x : EndInput) (h : endDecision x = .PASS)
    (p : PathView) (hm : p ∈ x.paths) : possible p = false := by
  have hc : worst (x.paths.map routeEnd) = .PASS :=
    end_requires_check x _ h (by simp [endChecks])
  apply (route_end_pass_iff p).mp
  exact (worst_pass_iff _).mp hc (routeEnd p) (List.mem_map.mpr ⟨p, hm, rfl⟩)

theorem residual_route_blocks_certificate (x : EndInput) (p : PathView)
    (hm : p ∈ x.paths) (hp : possible p = true) : endDecision x ≠ .PASS := by
  intro h
  have absent := end_requires_each_route_absent x h p hm
  simp [hp] at absent

theorem unknown_operation_blocks_certificate (x : EndInput) (hu : x.unknown ≠ 0) :
    endDecision x ≠ .PASS := by
  intro h
  exact hu (end_requires_closed_operations x h).2

theorem pending_operation_blocks_certificate (x : EndInput) (hp : x.pending ≠ 0) :
    endDecision x ≠ .PASS := by
  intro h
  exact hp (end_requires_closed_operations x h).1

theorem incomplete_inventory_blocks_certificate (x : EndInput) (hi : x.inventoryKnown = false) :
    endDecision x ≠ .PASS := by
  intro h
  have complete := (end_requires_complete_inventory x h).1
  simp [hi] at complete

theorem retained_audit_requires_exception (x : EndInput) (h : endDecision x = .PASS)
    (hr : x.retainedBody = true) : x.auditException = true := by
  have hc : checked (!x.retainedBody || x.auditException) = .PASS :=
    end_requires_check x _ h (by simp [endChecks])
  have hb := (checked_pass_iff _).mp hc
  simpa [hr] using hb

structure CertificateInput where
  historicalOK : Bool
  sameState : Bool
  sameScope : Bool
  withinTime : Bool
  savedVersion : Nat
  liveVersion : Nat
  savedEpoch : Nat
  liveEpoch : Nat
  termination : EndInput
  deriving DecidableEq, Repr

def certificateCurrent (x : CertificateInput) : Bool :=
  decide (x.historicalOK = true ∧ x.sameState = true ∧ x.sameScope = true ∧
    x.withinTime = true ∧ x.savedVersion = x.liveVersion ∧ x.savedEpoch = x.liveEpoch ∧
    endDecision x.termination = .PASS)

theorem current_requires_same_version (x : CertificateInput) (h : certificateCurrent x = true) :
    x.savedVersion = x.liveVersion := (of_decide_eq_true h).2.2.2.2.1

theorem current_requires_same_epoch (x : CertificateInput) (h : certificateCurrent x = true) :
    x.savedEpoch = x.liveEpoch := (of_decide_eq_true h).2.2.2.2.2.1

theorem current_requires_end_recheck (x : CertificateInput) (h : certificateCurrent x = true) :
    endDecision x.termination = .PASS := (of_decide_eq_true h).2.2.2.2.2.2

theorem stale_version_cannot_apply (x : CertificateInput) (hv : x.savedVersion ≠ x.liveVersion) :
    certificateCurrent x = false := by
  cases hc : certificateCurrent x with
  | false => rfl
  | true => exact False.elim (hv (current_requires_same_version x hc))

theorem changed_generation_cannot_apply (x : CertificateInput) (hg : x.savedEpoch ≠ x.liveEpoch) :
    certificateCurrent x = false := by
  cases hc : certificateCurrent x with
  | false => rfl
  | true => exact False.elim (hg (current_requires_same_epoch x hc))

theorem changed_state_cannot_apply (x : CertificateInput) (hs : x.sameState = false) :
    certificateCurrent x = false := by simp [certificateCurrent, hs]

theorem expired_certificate_cannot_apply (x : CertificateInput) (ht : x.withinTime = false) :
    certificateCurrent x = false := by simp [certificateCurrent, ht]

inductive Action where
  | none | managedRead | scopedEndRecord | realNetwork | physicalErasure
  deriving DecidableEq, Repr

def useAction (s : Status) : Action := if s = .PASS then .managedRead else .none

def endAction (s : Status) : Action := if s = .PASS then .scopedEndRecord else .none

theorem only_pass_supplies_content (s : Status) :
    useAction s = .managedRead ↔ s = .PASS := by cases s <;> decide

theorem only_pass_issues_end_record (s : Status) :
    endAction s = .scopedEndRecord ↔ s = .PASS := by cases s <;> decide

theorem end_record_is_not_erasure (s : Status) :
    endAction s ≠ .physicalErasure := by cases s <;> decide

theorem model_does_not_authorize_network (s : Status) :
    useAction s ≠ .realNetwork := by cases s <;> decide

/-- 再検証は結論の一致を検査する。HOLDをPASSへ昇格させるものではない。 -/
def replayCheck (computed recorded : Status) (evidenceOK : Bool) : Bool :=
  decide (evidenceOK = true ∧ recorded = computed)

theorem replay_preserves_decision (computed recorded : Status) (evidenceOK : Bool)
    (h : replayCheck computed recorded evidenceOK = true) : recorded = computed :=
  (of_decide_eq_true h).2

theorem changed_decision_fails_replay (computed recorded : Status) (evidenceOK : Bool)
    (h : recorded ≠ computed) : replayCheck computed recorded evidenceOK = false := by
  simp [replayCheck, h]

theorem hold_replay_is_not_release :
    replayCheck .HOLD .HOLD true = true ∧ useAction .HOLD = .none := by decide

end CivicLifecycleAssurance
