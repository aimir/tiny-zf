"""Install the checked nonempty-PC startup and protected-stack source bridge.

This is an untrusted proof-source adapter. Coq checks the literal bootstrap,
all affected interpreter proofs, and all three final set-theory theorems.
"""
import hashlib
from pathlib import Path

PC = tuple(bit == '1' for bit in '11101001001010001000011011011')
CAPACITY = 57
TAIL = (0,) * 615 + (1,) + (0,) * 3
REGISTERS = (3, 1, 6, 1, 0, 0, 0, 0, 0) + TAIL
STEPS = 2_187_238
PHYSICAL_OF = (6, 8, 0, 1, 3, 7, 2, 4, 5)
PHYSICAL_ORDER = (2, 3, 6, 4, 7, 8, 0, 5, 1)
TAIL_COQ = '(repeat 0 615 ++ [1] ++ repeat 0 3)'


def listing(values):
    return '[' + '; '.join('true' if x is True else 'false' if x is False
                           else str(x) for x in values) + ']'


def install(directory, startup_installer, replace_exact):
    """Extend the shared-startup kernel with its exact protected entry proof."""
    dirty, adjustments = startup_installer(directory)
    # That mode's source-prefix bridge is replaced below; only its arithmetic
    # proofs are reused by protected startup.
    adjustments = [item for item in adjustments
                   if not item.startswith('exact initial registers encode s3')]
    tm = directory / 'coq/tm'
    boot = tm / 'Boot.v'
    replace_exact(boot,
        'Definition boot_regs : list nat := [0; 1; 0; 0; 0; 0; 3; 0; 0] ++ repeat 0 95.',
        'Definition boot_pc : list bool := ' + listing(PC) + '.\n'
        'Definition boot_regs : list nat := ' + listing(REGISTERS[:9])
        + ' ++ ' + TAIL_COQ + '.', 1)
    replace_exact(boot, 'zeros 40 ++ true :: sepsR boot_regs',
                            'boot_pc ++ zeros 28 ++ true :: sepsR boot_regs', 1)
    # Keep certified computation opaque when composing its reachability proof;
    # otherwise the kernel can unnecessarily unfold millions of steps again.
    wrapper = f'''Definition boot_run : option lconf := lrunp {STEPS} (0, [], []).
Lemma boot_run_sound s' : boot_run = Some s' -> c0 -->* lconc s'.
Proof.
  unfold boot_run.
  change (lrunp {STEPS} (0, [], []) = Some s' -> lconc (0, [], []) -->* lconc s').
  apply lrunp_sound.
Qed.

'''
    replace_exact(boot, 'Definition boot_ok : bool :=',
                            wrapper + 'Definition boot_ok : bool :=', 1)
    replace_exact(boot, f'match lrunp {STEPS} (0, [], []) with',
                            'match boot_run with', 1)
    replace_exact(boot, '(* the blank tape is [zc (st 0) [] []] *)',
                            'Global Opaque boot_run.\n\n'
                            '(* the blank tape is [zc (st 0) [] []] *)', 1)
    replace_exact(boot, f'destruct (lrunp {STEPS} (0, [], []))',
                            'destruct boot_run', 1)
    replace_exact(boot,
        'apply lrunp_sound in E. simpl in E. change c0 with (zc (st 0) [] []).',
        'apply boot_run_sound in E. simpl in E.', 1)
    source = boot.read_text()
    boot.write_text('''(** Exact blank-tape bootstrap: 2,187,238 literal steps to state 96.
    The right tape is the 29-bit [boot_pc], 28 zero cells, the header,
    nine physical registers [3;1;6;1;0;0;0;0;0], and all 619 inactive
    registers, including their nonzero cell. No trailing data is discarded. *)
''' + source[source.index('From Coq Require Import'):])

    check = tm / 'Check254.v'
    replace_exact(check, '[2; 4; 3; 7; 6; 8; 0; 1; 5]',
                            listing(PHYSICAL_ORDER), 1)
    replace_exact(check, '[6; 7; 0; 2; 1; 8; 4; 3; 5]',
                            listing(PHYSICAL_OF), 1)

    sim = tm / 'Sim.v'
    source = sim.read_text().replace('R0', 'seed_regs')
    marker = '(** ** The site theorems'
    position = source.index(marker)
    source = source[:position] + '''(** The logical register file at the exact nonempty boot PC. *)
Definition seed_regs : regs := upd (upd (upd (upd regs0 2 3) 3 1) 4 1) 6 6.

''' + source[position:]
    source = source.replace('([], seed_regs)', '(boot_pc, seed_regs)')
    source = source.replace('exists (@nil bool), seed_regs, 40, (repeat 0 95).',
                            'exists boot_pc, seed_regs, 28, ' + TAIL_COQ + '.')
    helpers = '''(** The actual boot PC contains no stray nonzero bits after its selected leaf. *)
Lemma boot_pc_clean : clean p254 boot_pc.
Proof.
  intros e d W i Hi.
  vm_compute in W. injection W as <- <-.
  unfold bit, boot_pc. apply nth_overflow. simpl in Hi. simpl. lia.
Qed.

(** Clean PCs are preserved from this nonempty entry by every RM step. *)
Lemma no_stray_boot N P R e d :
  rm_run p254 N (boot_pc, seed_regs) = Some (P, R) ->
  walk p254 (nnodes p254 + 1) (root p254) P 0 = Some (e, d) ->
  Forall (fun b => b = false) (skipn d P).
Proof.
  intros Hr Wk. apply forall_skipn.
  destruct (run_reach p254 N _ _ Hr) as [E | ([P0 R1] & Es)].
  - injection E as -> ->. exact (boot_pc_clean e d Wk).
  - exact (step_clean p254 P0 R1 P R Es e d Wk).
Qed.

'''
    source = source.replace('Lemma inv_view ', helpers + 'Lemma inv_view ', 1)
    source = source.replace("no_stray p254 seed_regs N P' Rg' e d Hr W",
                            "no_stray_boot N P' Rg' e d Hr W")
    sim.write_text(source)

    main = tm / 'Main.v'
    source = main.read_text().replace('([], R0)', '(boot_pc, seed_regs)')
    # The upstream iter corollary concerns the empty root PC and is inapplicable
    # here. The complete source bridge below starts at the actual boot entry.
    source = source[:source.index('Corollary tm254_iter :')]
    source = '''(** The literal machine halts iff the RM halts from its exact boot PC and registers. *)
''' + source[source.index('From Coq Require Import'):]
    main.write_text(source)

    here = Path(__file__).resolve().parent
    additions = {
        'general_initialization.v': directory / 'coq/logic/GeneralInit.v',
        'stack_protection.v': directory / 'coq/logic/StackProtection.v',
        'protected_startup.v': directory / 'coq/prog/ProtectedStartup.v',
    }
    for filename, target in additions.items():
        content = (here / filename).read_text()
        if filename == 'stack_protection.v':
            content = content.replace('Require Import GeneralInit.',
                                      'From M254L Require Import GeneralInit.')
        target.write_text(content)
        dirty.add(target.resolve())
        adjustments.append(filename + ' SHA256 ' + hashlib.sha256(
            (here / filename).read_bytes()).hexdigest())

    e2e = directory / 'coq/e2e/E2E254.v'
    replace_exact(e2e, 'From M254P Require Main254.',
                            'From M254P Require ProtectedStartup.', 1)
    replace_exact(e2e,
        'rewrite M254.Main.tm254_rm, M254P.Main254.prog254, M254L.L1_254.L1_254.',
        'rewrite M254P.ProtectedStartup.tm250_thm.', 1)
    source = e2e.read_text()
    e2e.write_text('''(** The exact 250-state blank-tape machine halts iff conventional ZF,
    ZFC, or SIR is inconsistent. ProtectedStartup proves the literal
    tape-to-calculus chain; the existing theory bridges are unchanged.
    Historical theorem names retain the suffix 254. *)
''' + source[source.index('From Undecidability.FOL'):])
    dirty.update(path.resolve() for path in (boot, check, sim, main, e2e))
    adjustments.extend([
        'physical register permutation [0,3,1,4,2,5,6,8,7]; all instruction sites rechecked',
        'nonempty 29-bit boot PC with capacity 57 and exact 619-register inactive tail',
        'two candidate RM steps, certificate entry 148, and 347 original-source RM steps',
        'unbounded structured AX suffix, three return steps, and protected initial stack at candidate zero',
    ])
    return dirty, adjustments
