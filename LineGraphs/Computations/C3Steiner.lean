/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ModelCertificates
import LineGraphs.Computations.C3ARows00
import LineGraphs.Computations.C3ARows01
import LineGraphs.Computations.C3ARows02
import LineGraphs.Computations.C3ARows03
import LineGraphs.Computations.C3ARows04
import LineGraphs.Computations.C3ARows05
import LineGraphs.Computations.C3ARows06
import LineGraphs.Computations.C3ARows07
import LineGraphs.Computations.C3ARows08
import LineGraphs.Computations.C3ARows09
import LineGraphs.Computations.C3ARows10
import LineGraphs.Computations.C3ARows11
import LineGraphs.Computations.C3SteinerRows00
import LineGraphs.Computations.C3SteinerRows01
import LineGraphs.Computations.C3SteinerRows02
import LineGraphs.Computations.C3SteinerRows03
import LineGraphs.Computations.C3SteinerRows04
import LineGraphs.Computations.C3SteinerRows05
import LineGraphs.Computations.C3SteinerRows06
import LineGraphs.Computations.C3SteinerRows07
import LineGraphs.Computations.C3SteinerRows08
import LineGraphs.Computations.C3SteinerRows09
import LineGraphs.Computations.C3SteinerRows10
import LineGraphs.Computations.C3SteinerRows11

/-!
# C3 isomorphism

The two isomorphisms of computation C3, from the Sage root maps. -/

open Computations

namespace Computations.C3

theorem steiner_gram_checked : (List.range 240).all
    (checkScaledGramRow 2 4 e₈SteinerRoots steinerImages) = true := by
  apply all_eq_true_of_chunks
    (chunk := fun k => (List.range 240).drop (20 * k) |>.take 20) (m := 12)
    (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 12).all steinerGramChunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    steiner_gram_chunk_0,
    steiner_gram_chunk_1,
    steiner_gram_chunk_2,
    steiner_gram_chunk_3,
    steiner_gram_chunk_4,
    steiner_gram_chunk_5,
    steiner_gram_chunk_6,
    steiner_gram_chunk_7,
    steiner_gram_chunk_8,
    steiner_gram_chunk_9,
    steiner_gram_chunk_10,
    steiner_gram_chunk_11, Bool.and_self]

theorem steiner_images_perm : steinerImages.Perm E₈Data.e₈Roots := by
  have hs : steinerImages.insertionSort
      (fun v w => vectorKey v ≤ vectorKey w) = E₈Data.e₈Roots := by
    decide +kernel
  rw [← hs]
  exact (List.perm_insertionSort _ _).symm

theorem steiner_images_set : steinerImages.toFinset = E₈Data.e₈Roots.toFinset := by
  ext w
  simpa using steiner_images_perm.mem_iff (a := w)

/-- Target presentation in the order prescribed by the Sage map. -/
@[instance_reducible] noncomputable def steinerTarget : LineSystem.IntegerModel LineSystem.E₈ :=
  LineSystem.E₈viaD₈.integerModel.ofTable steinerImages 240 (by decide +kernel)
    (steiner_images_perm.nodup_iff.mpr (of_decide_eq_true E₈Data.e₈_nodup_checked))
    (fun w => (mem_iff_of_toFinset_eq steiner_images_set w).trans
      (LineSystem.E₈viaD₈.mem_rootList w))

end Computations.C3

namespace LineSystem

/-- C3: the isomorphism sending the `i`-th root of `e₈SteinerRoots` to the `i`-th entry of
`C3.steinerImages`, which preserves the Gram matrix up to the scale `C3.steiner_gram_checked`. The
images are those of the Sage map `maps[1]` of `cgss/certificates/data/c03_maps.json`
(`E8_S` to `E8_D`, as row vectors), which `scripts/generate_c3.py` checks; Lean checks only
the root correspondence, and the iso is not stated as induced by the matrix. -/
noncomputable def E₈viaSteiner.isoE₈ : E₈viaSteiner.Iso E₈ :=
  Iso.ofIntegerModels
    (E₈viaSteiner.integerModel.ofTable e₈SteinerRoots 240 (by decide +kernel) e₈SteinerRoots_nodup
      E₈viaSteiner.mem_rootList)
    C3.steinerTarget (Equiv.refl _) fun i j =>
      checkScaledGram_sound (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) C3.steiner_gram_checked i j

/-- C3: existence of the isomorphism between this presentation and the default E₈. -/
theorem E₈viaSteiner.nonempty_iso_E₈ : Nonempty (E₈viaSteiner.Iso E₈) := ⟨E₈viaSteiner.isoE₈⟩

end LineSystem
