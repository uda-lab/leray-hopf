-- Collision-fixture self-test (issue #212 B0 codex-gate pass-7 finding 1;
-- companion of scripts/scratch_reader.lean — same static trust model: imports
-- only `Lean`, reads the fixture olean as data, executes nothing fixture-authored).
--
-- Run via:
--   lake env lean scripts/scratch_fixture_selftest.lean
-- (after `lake build LerayHopf.Scratch.GateFixture`; consumed by
-- scripts/check-scratch-pins.sh, which requires the FIXTURE-SELFTEST-OK line.)
--
-- Asserts that every deliberately collision-named hand-written declaration in
-- LerayHopf/Scratch/GateFixture.lean is enumerated by `ModuleData.constNames` —
-- the same channel the gate manifest is built from.  This is the mechanical
-- evidence that a hand-written `P.ibelow` / `C.mk.noConfusionType` /
-- `d.congr_simp` / `P.proof_1` cannot hide from the total-manifest pinning:
-- had any of these been declared in a gate target, it would surface as a new
-- DECL line and fail the byte-diff against scratch-manifest.expected.
import Lean

open Lean

def fixtureMod : Name := `LerayHopf.Scratch.GateFixture

def collisions : List Name := [
  `LerayHopf.ScratchFixture.Probe.ibelow,
  `LerayHopf.ScratchFixture.Probe.mk.noConfusionType,
  `LerayHopf.ScratchFixture.Probe.proof_1]
-- (`probeDef.congr_simp` is absent deliberately: the def-parent companion
-- suffixes are reserved names on this toolchain and cannot be collision-declared
-- at all — see the negative-fixture note in GateFixture.lean.)

def main' : IO Unit := do
  let path ← findOLean fixtureMod
  let (md, _region) ← readModuleData path
  let mut missing := 0
  for c in collisions do
    if md.constNames.contains c then
      IO.println s!"FIXTURE-ENUMERATED|{c}"
    else
      IO.println s!"FIXTURE-MISSING|{c}"
      missing := missing + 1
  if missing == 0 then
    IO.println "FIXTURE-SELFTEST-OK"
  else
    throw <| IO.userError s!"fixture self-test: {missing} collision declaration(s) not enumerated"

#eval main'
