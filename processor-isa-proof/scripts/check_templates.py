#!/usr/bin/env python3
"""Compile the portable templates outside the skill, audit assumptions, coqchk.

This checks the shipped templates/examples, not a target processor or its adapter.
Uses only the Python standard library. Override tool paths for an opam switch.
"""
import argparse
import hashlib
import json
import pathlib
import shutil
import subprocess
import tempfile

MODULES = ["CycleRefinement", "RegisterEffects", "CheckerFacts", "EvaluationFacts",
           "RankedSettling", "Examples"]
THEOREMS = {
    "CycleRefinement": ["invariant_execution", "lift_view_invariant", "simulate_execution"],
    "RegisterEffects": ["effect_preserves_agreement", "effect_preserves_zero",
                        "read_forwarded_write", "read_unaffected"],
    "CheckerFacts": ["guarded_checker", "disabled_checker", "same_bits_width", "numeric_checker"],
    "EvaluationFacts": ["write_preserves_other", "write_preserves_reads",
                        "eval_after_unrelated_write", "fixed_point_iterations", "iterate_add",
                        "settled_after_prefix"],
    "RankedSettling": ["ranks_valid_sound", "ranked_history", "ranked_history_bounded"],
    "Examples": ["IncrementPipeline.refinement", "IncrementPipeline.two_retirements_with_stall",
                 "Forwarding.write_then_read", "Forwarding.zero_is_protected",
                 "Forwarding.preview_banks_agree", "Checker.enabled_correct",
                 "Checker.unequal_widths_same_numeric_value", "Settling.finite_prefix", "Settling.stable_tail",
                 "Settling.budget_is_not_fixed", "Cone.certificate", "Cone.propagation", "Cone.bounded_propagation",
                 "Frame.other_write", "PreviewChecker.enabled_preview_checker"],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coqc", default="coqc")
    parser.add_argument("--coqchk", default="coqchk")
    parser.add_argument("--build-dir", type=pathlib.Path,
                        help="Existing empty or new directory outside the skill; default: temporary directory")
    parser.add_argument("--timeout", type=int, default=180, help="Seconds per tool invocation")
    args = parser.parse_args()
    skill = pathlib.Path(__file__).resolve().parents[1]
    for tool in (args.coqc, args.coqchk):
        if not shutil.which(tool):
            parser.error(f"Tool not found: {tool}")
    build = (args.build_dir or pathlib.Path(tempfile.mkdtemp(prefix="processor-proof-"))).resolve()
    if build == skill or skill in build.parents:
        parser.error("Build directory must be outside the skill")
    build.mkdir(parents=True, exist_ok=True)
    if any(build.iterdir()):
        parser.error(f"Build directory must be empty: {build}")
    print(f"Build directory: {build}", flush=True)

    def run(command, log):
        try:
            result = subprocess.run(command, cwd=build, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, timeout=args.timeout)
        except subprocess.TimeoutExpired as error:
            raise SystemExit(f"Timed out: {command[0]} ({log})") from error
        (build / log).write_text(result.stdout)
        if result.returncode:
            raise SystemExit(f"Failed: {' '.join(command)}\n{result.stdout[-5000:]}\nLog: {build / log}")
        return result.stdout

    version = run([args.coqc, "--version"], "version.log").strip()
    flags = ["-Q", str(build), "ProcessorProof"]
    for module in MODULES:
        shutil.copy2(skill / "assets" / "coq" / f"{module}.v", build)
        run([args.coqc, *flags, f"{module}.v"], f"{module}.log")
        print(f"Compiled {module}", flush=True)
    audit_names = [f"{module}.{name}" for module, names in THEOREMS.items() for name in names]
    (build / "AssumptionAudit.v").write_text(
        "From ProcessorProof Require Import " + " ".join(MODULES) + ".\n" +
        "\n".join(f"Print Assumptions {name}." for name in audit_names) + "\n")
    audit = run([args.coqc, *flags, "AssumptionAudit.v"], "assumptions.log")
    # Explicit section hypotheses become theorem arguments, not global assumptions.
    if "Axioms:" in audit or audit.count("Closed under the global context") != len(audit_names):
        raise SystemExit(f"Unexpected assumption report; inspect {build / 'assumptions.log'}")
    run([args.coqchk, "-silent", *flags,
         *[f"ProcessorProof.{m}" for m in MODULES], "ProcessorProof.AssumptionAudit"], "coqchk.log")
    report = {"compiler": version, "modules": MODULES, "assumptions_audited": audit_names,
              "coqc_tool": shutil.which(args.coqc), "coqchk_tool": shutil.which(args.coqchk),
              "source_sha256": {m + ".v": hashlib.sha256((build / (m + ".v")).read_bytes()).hexdigest()
                                for m in MODULES},
              "all_audited_theorems_closed": True, "coqchk_passed": True,
              "scope": "Portable templates and examples only; no DUT correctness claim"}
    (build / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(MODULES)} modules; {len(audit_names)} assumption audits; coqchk passed.")
    print(f"Report: {build / 'report.json'}")


if __name__ == "__main__":
    main()
