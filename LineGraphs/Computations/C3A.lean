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

theorem a_gram_checked : (List.range 240).all
    (checkScaledGramRow 9 4 e₈ARoots aImages) = true := by
  apply all_eq_true_of_chunks
    (chunk := fun k => (List.range 240).drop (20 * k) |>.take 20) (m := 12)
    (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 12).all aGramChunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    a_gram_chunk_0,
    a_gram_chunk_1,
    a_gram_chunk_2,
    a_gram_chunk_3,
    a_gram_chunk_4,
    a_gram_chunk_5,
    a_gram_chunk_6,
    a_gram_chunk_7,
    a_gram_chunk_8,
    a_gram_chunk_9,
    a_gram_chunk_10,
    a_gram_chunk_11, Bool.and_self]

theorem a_images_perm : aImages.Perm E₈Data.e₈Roots := by
  have hs : aImages.insertionSort
      (fun v w => vectorKey v ≤ vectorKey w) = E₈Data.e₈Roots := by
    decide +kernel
  rw [← hs]
  exact (List.perm_insertionSort _ _).symm

theorem a_images_set : aImages.toFinset = E₈Data.e₈Roots.toFinset := by
  ext w
  simpa using a_images_perm.mem_iff (a := w)

/-- Target presentation in the order prescribed by the Sage map. -/
@[instance_reducible] noncomputable def aTarget : LineSystem.IntegerModel LineSystem.E₈ :=
  LineSystem.E₈viaD₈.integerModel.ofTable aImages 240 (by decide +kernel)
    (a_images_perm.nodup_iff.mpr (of_decide_eq_true E₈Data.e₈_nodup_checked))
    (fun w => (mem_iff_of_toFinset_eq a_images_set w).trans
      (LineSystem.E₈viaD₈.mem_rootList w))

end Computations.C3

namespace LineSystem

/-- C3: the isomorphism sending the `i`-th root of `e₈ARoots` to the `i`-th entry of
`C3.aImages`, which preserves the Gram matrix up to the scale `C3.a_gram_checked`. The
images are those of the Sage map `maps[0]` of `cgss/certificates/data/c03_maps.json`
(`E8_A` to `E8_D`, as row vectors), which `scripts/generate_c3.py` checks; Lean checks only
the root correspondence, and the iso is not stated as induced by the matrix. -/
noncomputable def E₈viaA₈.isoE₈ : E₈viaA₈.Iso E₈ :=
  Iso.ofIntegerModels
    (E₈viaA₈.integerModel.ofTable e₈ARoots 240 (by decide +kernel) e₈ARoots_nodup
      E₈viaA₈.mem_rootList)
    C3.aTarget (Equiv.refl _) fun i j =>
      checkScaledGram_sound (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) C3.a_gram_checked i j

/-- C3: existence of the isomorphism between this presentation and the default E₈. -/
theorem E₈viaA₈.nonempty_iso_E₈ : Nonempty (E₈viaA₈.Iso E₈) := ⟨E₈viaA₈.isoE₈⟩

end LineSystem
