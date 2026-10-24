import CivicAnswerAdoption
import CivicPrivacyAssurance
import CivicLifecycleAssurance

/-!
# 共通合成プロファイルの合成境界
Copyright © 2026 AI Assurance, Inc. All rights reserved. See README.md.

Proof scope: no registration/supply without all prerequisite decisions and bindings.
The original three model files are imported unchanged. Atomic observations (actual
bytes, identities, origins and current-state facts) are trusted model inputs; this
file does not prove Python, transport, authentication, source truth, or deletion.
Missing/unexecuted stages are NOT_RUN, never PASS. No sorry or extra axioms.
-/
set_option autoImplicit false
set_option warningAsError true
namespace CivicBridge

inductive Status where
  | PASS | HOLD | REJECT | NOT_RUN
  deriving DecidableEq, Repr

structure Observation where
  send : Status
  output : Status
  answer : Status
  sameRequest : Bool
  sameAnswer : Bool
  originsBound : Bool
  registered : Bool
  use : Status
  actionOk : Bool
  deriving DecidableEq, Repr

def isPass (s : Status) : Bool := decide (s = .PASS)

def mayRegister (o : Observation) : Bool :=
  isPass o.send && isPass o.output && isPass o.answer &&
    o.sameRequest && o.sameAnswer && o.originsBound

def maySupply (o : Observation) : Bool :=
  mayRegister o && o.registered && isPass o.use && o.actionOk

theorem register_iff (o : Observation) :
    mayRegister o = true ↔ o.send = .PASS ∧ o.output = .PASS ∧
      o.answer = .PASS ∧ o.sameRequest = true ∧ o.sameAnswer = true ∧ o.originsBound = true := by
  simp [mayRegister, isPass, and_assoc]

theorem supply_iff (o : Observation) :
    maySupply o = true ↔ mayRegister o = true ∧ o.registered = true ∧
      o.use = .PASS ∧ o.actionOk = true := by
  simp [maySupply, isPass, and_assoc]

theorem register_requires_send (o : Observation) (h : mayRegister o = true) : o.send = .PASS := by
  cases hs : o.send <;> simp_all [mayRegister, isPass]

theorem register_requires_output (o : Observation) (h : mayRegister o = true) : o.output = .PASS := by
  cases hs : o.output <;> simp_all [mayRegister, isPass]

theorem register_requires_answer (o : Observation) (h : mayRegister o = true) : o.answer = .PASS := by
  cases hs : o.answer <;> simp_all [mayRegister, isPass]

theorem supply_requires_send (o : Observation) (h : maySupply o = true) : o.send = .PASS := by
  cases hs : o.send <;> simp_all [maySupply, mayRegister, isPass]

theorem supply_requires_output (o : Observation) (h : maySupply o = true) : o.output = .PASS := by
  cases hs : o.output <;> simp_all [maySupply, mayRegister, isPass]

theorem supply_requires_answer (o : Observation) (h : maySupply o = true) : o.answer = .PASS := by
  cases hs : o.answer <;> simp_all [maySupply, mayRegister, isPass]

theorem supply_requires_current_use (o : Observation) (h : maySupply o = true) : o.use = .PASS := by
  cases hs : o.use <;> simp_all [maySupply, mayRegister, isPass]

theorem supply_requires_registration (o : Observation) (h : maySupply o = true) : o.registered = true := by
  cases hs : o.registered <;> simp_all [maySupply, mayRegister, isPass]

theorem no_cross_request_supply (o : Observation) (h : o.sameRequest = false) : maySupply o = false := by
  simp [maySupply, mayRegister, h]

theorem no_replaced_answer_supply (o : Observation) (h : o.sameAnswer = false) : maySupply o = false := by
  simp [maySupply, mayRegister, h]

theorem no_unbound_origin_supply (o : Observation) (h : o.originsBound = false) : maySupply o = false := by
  simp [maySupply, mayRegister, h]

theorem no_failed_action_supply (o : Observation) (h : o.actionOk = false) : maySupply o = false := by
  simp [maySupply, h]

theorem no_skipped_answer_supply (o : Observation) (h : o.answer = .NOT_RUN) : maySupply o = false := by
  simp [maySupply, mayRegister, isPass, h]

theorem no_held_send_registration (o : Observation) (h : o.send = .HOLD) : mayRegister o = false := by
  simp [mayRegister, isPass, h]

theorem no_rejected_output_registration (o : Observation) (h : o.output = .REJECT) : mayRegister o = false := by
  simp [mayRegister, isPass, h]

theorem no_ended_use_supply (o : Observation) (h : o.use = .REJECT) : maySupply o = false := by
  simp [maySupply, isPass, h]

example : CivicPrivacyAssurance.referenceSHA256 =
  "7ad18cd83dc87acbca7ca0895d64e74b68b1c7e4df461e0800c8e301571aeda7" := by decide
example : CivicLifecycleAssurance.referenceSHA256 =
  "e385c4c4379207b92355a2621f14422e4337e20fe4b2c7ba6f2407245f5a0add" := by decide

#print axioms register_iff
#print axioms supply_iff
#print axioms register_requires_send
#print axioms register_requires_output
#print axioms register_requires_answer
#print axioms supply_requires_send
#print axioms supply_requires_output
#print axioms supply_requires_answer
#print axioms supply_requires_current_use
#print axioms supply_requires_registration
#print axioms no_cross_request_supply
#print axioms no_replaced_answer_supply
#print axioms no_unbound_origin_supply
#print axioms no_failed_action_supply
#print axioms no_skipped_answer_supply
#print axioms no_held_send_registration
#print axioms no_rejected_output_registration
#print axioms no_ended_use_supply
end CivicBridge
