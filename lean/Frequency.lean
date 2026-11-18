import Std

/-! Cut and multiplicity bounds for words containing every permutation. -/
namespace Supersequence
open List
variable {α : Type}

/-- Every repetition-free request using letters in A embeds in w. -/
def Covers (A : α → Prop) (w : List α) : Prop :=
  ∀ q : List α, q.Nodup → (∀ a ∈ q, A a) → q.Sublist w

private theorem splitAtRequest {u v l r : List α} (h : (u ++ v).Sublist (l ++ r)) :
    u.Sublist l ∨ v.Sublist r := by
  obtain ⟨i,j,e,hi,hj⟩ := sublist_append_iff.mp h
  rcases append_eq_append_iff.mp e with ⟨k,hk,_⟩ | ⟨k,_,hk⟩
  · exact .inl ((sublist_append_left u k).trans (hk ▸ hi))
  · subst j
    exact .inr ((sublist_append_right k v).trans hj)

theorem skipGap {x : α} {v g r : List α} (hx : x ∉ g)
    (h : (x :: v).Sublist (g ++ r)) : (x :: v).Sublist r := by
  induction g with
  | nil => exact h
  | cons a g ih =>
    have hxa : x ≠ a := by intro e; exact hx (by simp [e])
    apply ih (fun hm => hx (.tail _ hm))
    rcases sublist_cons_iff.mp h with h | ⟨s,he,_⟩
    · exact h
    · simp_all

/-- Any embedding chooses its pivot on one side of a pivot-free gap. -/
theorem cut {x : α} {u v l g r : List α} (hx : x ∉ g)
    (h : (u ++ x :: v).Sublist (l ++ (g ++ r))) : u.Sublist l ∨ v.Sublist r := by
  rcases splitAtRequest h with hl | hr
  · exact .inl hl
  · exact .inr (sublist_of_cons_sublist (skipGap hx hr))

/-- Complementary alphabets cannot both have a missing order. -/
theorem complementaryCut {x : α} {l g r : List α} (hx : x ∉ g)
    (univ : Covers (fun _ => True) (l ++ (g ++ r))) (S : α → Prop) :
    Covers (fun a => a ≠ x ∧ S a) l ∨ Covers (fun a => a ≠ x ∧ ¬ S a) r := by
  classical
  apply Classical.or_iff_not_imp_left.mpr
  intro fail v hv av
  simp only [Covers, Classical.not_forall] at fail
  obtain ⟨u, hu, au, missing⟩ := fail
  have distinct : (u ++ x :: v).Nodup := by
    simp only [nodup_append, nodup_cons, mem_cons]
    grind
  exact (cut hx (univ _ distinct (by simp))).resolve_left missing

private theorem insertPivot {x : α} {u v : List α} (hn : (u ++ v).Nodup)
    (hx : x ∉ u ++ v) : (u ++ x :: v).Nodup := by
  simp only [nodup_append, nodup_cons, mem_cons, mem_append] at *
  grind

/-- Replace a pivot-free gap by one copy of each old letter. Greedily extend
the request on the left, then use the first failed letter in the bridge. -/
theorem bridge {x : α} {l g r alphabet : List α} (hx : x ∉ g)
    (letters : ∀ a, a ≠ x → a ∈ alphabet)
    (h : Covers (fun _ => True) (l ++ (g ++ r))) :
    Covers (fun a => a ≠ x) (l ++ (alphabet ++ r)) := by
  intro q hn hq
  suffices go : ∀ (tail pre : List α), q = pre ++ tail → pre.Sublist l →
      q.Sublist (l ++ (alphabet ++ r)) by
    exact go q [] rfl (nil_sublist _)
  intro tail
  induction tail with
  | nil =>
    intro pre he hl
    simpa [he] using (sublist_append_of_sublist_left (l₂ := alphabet ++ r) hl)
  | cons a t ih =>
    intro pre he hl
    by_cases ht : (pre ++ [a]).Sublist l
    · exact ih (pre ++ [a]) (by simpa [append_assoc] using he) ht
    · have he' : q = (pre ++ [a]) ++ t := by simpa [append_assoc] using he
      have hxq : x ∉ q := fun mem => hq x mem rfl
      have hp := insertPivot (x := x) (he' ▸ hn) (he' ▸ hxq)
      have hr := (cut hx (h _ hp (by simp))).resolve_left ht
      have ha : a ∈ q := by simp [he]
      have one : [a].Sublist alphabet := singleton_sublist.mpr (letters a (hq a ha))
      simpa [he, append_assoc] using hl.append (one.append hr)

variable [DecidableEq α]

def project (x : α) (w : List α) := w.filter (· != x)

@[simp] theorem project_append (x : α) (a b : List α) :
    project x (a ++ b) = project x a ++ project x b := filter_append a b

@[simp] theorem project_cons_self (x : α) (w : List α) :
    project x (x :: w) = project x w := by simp [project]

def LowerOnOthers (x : α) (F : Nat) : Prop :=
  ∀ v : List α, x ∉ v → Covers (· ≠ x) v → F ≤ v.length

theorem project_free {x : α} {w : List α} (h : x ∉ w) : project x w = w := by
  apply filter_eq_self.mpr
  intro a ha
  simp only [bne_iff_ne]
  exact fun e => h (e ▸ ha)

theorem projected_bound {x : α} {w : List α} {F : Nat}
    (low : LowerOnOthers x F) (cov : Covers (· ≠ x) w) : F ≤ (project x w).length := by
  apply low _ (by simp [project])
  intro q hn hq
  have h := (cov q hn hq).filter (· != x)
  rw [show q.filter (· != x) = q from project_free (fun hm => hq x hm rfl)] at h
  exact h

omit [DecidableEq α] in
theorem front {x : α} {g r : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (g ++ r)) : Covers (· ≠ x) r := by
  intro q hn hq
  exact sublist_of_cons_sublist (skipGap hg (hw (x::q) (by
    simp [hn]; exact fun hm => hq x hm rfl) (by simp)))

omit [DecidableEq α] in
theorem back {x : α} {l g : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (l ++ g)) : Covers (· ≠ x) l := by
  intro q hn hq
  have h := hw (q ++ [x]) (by simp [nodup_append,hn]; grind) (by simp)
  exact (splitAtRequest h).resolve_right (fun hm => hg (singleton_sublist.mp hm))

theorem length_account (x : α) (w : List α) :
    (project x w).length + w.count x = w.length := by
  induction w with
  | nil => simp [project]
  | cons a w ih =>
    by_cases e : a = x
    · subst a; simp; omega
    · simpa [project, count_cons, e, Ne.symm e, Nat.add_right_comm] using ih

private def runs (x : α) (gs : List (List α)) := gs.flatMap (· ++ [x])

private theorem decompose (x : α) (w : List α) :
    ∃ gs t, w = runs x gs ++ t ∧ x ∉ t ∧ ∀ g ∈ gs, x ∉ g := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨gs,t,rfl,ht,hg⟩ := ih
    by_cases e : a = x
    · subst a; exact ⟨[] :: gs,t,by simp [runs],ht,by simpa using hg⟩
    · cases gs with
      | nil => exact ⟨[], a :: t, rfl, by simp [Ne.symm e,ht], by simp⟩
      | cons g gs =>
        exact ⟨(a::g) :: gs,t,rfl,ht,by
          intro v hv
          rcases mem_cons.mp hv with rfl | hv
          · simp [Ne.symm e,hg _ (.head _)]
          · exact hg _ (.tail _ hv)⟩

private theorem runs_account {x : α} {gs : List (List α)}
    (free : ∀ g ∈ gs, x ∉ g) :
    (runs x gs).count x = gs.length ∧
    (project x (runs x gs)).length = (gs.map List.length).sum := by
  induction gs with
  | nil => simp [runs,project]
  | cons g gs ih =>
    have ⟨hc,hl⟩ := ih (fun a ha => free a (.tail _ ha))
    have hf := project_free (free g (.head _))
    change (g ++ [x] ++ runs x gs).count x = _ ∧ (project x (g ++ [x] ++ runs x gs)).length = _
    simp [count_eq_zero.mpr (free g (.head _)),hc,hf,hl,project_cons_self]

omit [DecidableEq α] in
private theorem sum_le {gs : List (List α)} {B : Nat}
    (h : ∀ g ∈ gs, g.length ≤ B) : (gs.map List.length).sum ≤ gs.length * B := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun a ha => h a (.tail _ ha))
    have hh := h g (.head _)
    simp [Nat.succ_mul]; omega

/-- If r copies leave t old letters, then F+m ≤ r*(t-F+m), with F a
lower bound on the old alphabet and m the length of a list containing it. -/
theorem pivotInequality {w alphabet : List α} {x : α} {F : Nat}
    (hw : Covers (fun _ => True) w) (low : LowerOnOthers x F)
    (letters : ∀ a, a ≠ x → a ∈ alphabet) :
    F + alphabet.length ≤ w.count x * ((project x w).length - F + alphabet.length) := by
  have present : x ∈ w := singleton_sublist.mp (hw [x] (by simp) (by simp))
  obtain ⟨p,y,ew,hp⟩ := eq_append_cons_of_mem present
  obtain ⟨gs,t,ey,ht,hg⟩ := decompose x y
  let T := (project x w).length
  let B := T - F
  have oldlen : F ≤ T := projected_bound low (fun q hn _ => hw q hn (by simp))
  have gap_bound (l g r : List α) (eqn : w = l ++ (g ++ r)) (free : x ∉ g) :
      g.length ≤ B + alphabet.length := by
    have h := projected_bound low (bridge free letters (eqn ▸ hw))
    have hlen : T = (project x l).length + (g.length + (project x r).length) := by
      simp only [T,eqn,project_append,project_free free,length_append]
    have ha := length_filter_le (· != x) alphabet
    simp only [project,filter_append,length_append] at h hlen
    unfold B; omega
  have left_bound : p.length ≤ B := by
    have h := projected_bound low (front hp (ew ▸ hw))
    have ht' : T = p.length + (project x (x::y)).length := by
      simp only [T,ew,project_append,project_free hp,length_append]
    unfold B; omega
  have eqt : w = (p ++ x :: runs x gs) ++ t := by simp [ew,ey,append_assoc]
  have right_bound : t.length ≤ B := by
    have h := projected_bound low (back ht (eqt ▸ hw))
    have ht' : T = (project x (p ++ x :: runs x gs)).length + t.length := by
      simp only [T,eqt,project_append,project_free ht,length_append]
    unfold B; omega
  have bound := sum_le (gs := gs) (B := B + alphabet.length) (by
    intro g mem
    obtain ⟨a,b,e⟩ := append_of_mem mem
    apply gap_bound (p ++ x :: runs x a) g (x :: (runs x b ++ t)) _ (hg g mem)
    simp [ew,ey,e,runs,append_assoc])
  obtain ⟨hc,hl⟩ := runs_account hg
  have count : w.count x = gs.length + 1 := by
    simp [eqt,count_eq_zero.mpr hp,count_eq_zero.mpr ht,hc]
  have len : T = p.length + (gs.map List.length).sum + t.length := by
    simp only [T,eqt,project_append,project_cons_self,project_free hp,project_free ht,length_append,hl]
  rw [count]
  change F + alphabet.length ≤ (gs.length + 1) * (B + alphabet.length)
  rw [Nat.add_mul, Nat.one_mul]
  have split : B + F = T := by dsimp [B]; omega
  omega

/-- The ordinary statement about full permutations on a finite alphabet. -/
def Universal {n : Nat} (w : List (Fin n)) : Prop :=
  ∀ p : List (Fin n), p.Perm (finRange n) → p.Sublist w

theorem universal_iff_covers {w : List (Fin n)} :
    Universal w ↔ Covers (fun _ => True) w := by
  constructor
  · intro h q hq _
    let rest := (finRange n).filter (fun a => !q.contains a)
    have dis : (q ++ rest).Nodup := by
      apply nodup_append.mpr
      refine ⟨hq,(nodup_finRange n).sublist (filter_sublist),?_⟩
      intro a ha b hb eq
      simp [rest,← eq,ha] at hb
    have all : ∀ a, a ∈ q ++ rest := by
      intro a
      by_cases ha : a ∈ q <;> simp [rest,ha,mem_finRange]
    have hp : (q ++ rest).Perm (finRange n) := by
      apply perm_iff_count.mpr
      intro a
      rw [dis.count_of_mem (all a), (nodup_finRange n).count_of_mem (mem_finRange a)]
    exact (sublist_append_left q rest).trans (h _ hp)
  · intro h p hp
    exact h p (hp.nodup_iff.mpr (nodup_finRange n)) (by simp)

private def skip (x : Fin 10) (a : Fin 9) : Fin 10 :=
  if a.val < x.val then ⟨a.val,by omega⟩ else ⟨a.val+1,by omega⟩

private def close (x a : Fin 10) : Fin 9 :=
  ⟨(if a.val < x.val then a.val else a.val - 1) % 9, Nat.mod_lt _ (by decide)⟩

private theorem close_skip : ∀ x a, close x (skip x a) = a := by decide
private theorem skip_ne : ∀ x a, skip x a ≠ x := by decide

theorem transportNine (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    (x : Fin 10) : LowerOnOthers x 66 := by
  intro v _ hv
  have cov : Covers (fun _ => True) (v.map (close x)) := by
    intro q hn _
    have nd : (q.map (skip x)).Nodup := pairwise_map.mpr (hn.imp (by
      intro a b hab e; exact hab (by simpa only [close_skip] using congrArg (close x) e)))
    have h := (hv _ nd (by simpa using fun a (_ : a ∈ q) => skip_ne x a)).map (close x)
    have eq : (q.map (skip x)).map (close x) = q := by
      simp [map_map, Function.comp_def, close_skip]
    exact eq ▸ h
  simpa using nine _ (universal_iff_covers.mpr cov)

/-- The only numerical input is the lower bound on words over Fin 9. -/
theorem frequencySplit (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82) :
    (∀ x, 4 ≤ w.count x) ∧ (∃ x, w.count x ≤ 7) := by
  have cover := universal_iff_covers.mp hw
  constructor
  · intro x
    let A := (finRange 10).erase x
    have ha : A.length = 9 := by simp [A,length_erase_of_mem (mem_finRange x)]
    have h := pivotInequality (x := x) (alphabet := A) cover (transportNine nine x)
      (fun a ne => (mem_erase_of_ne ne).mpr (mem_finRange a))
    rw [ha] at h
    have account := length_account x w
    rcases Nat.lt_or_ge (w.count x) 4 with small | large
    · have cases : w.count x = 0 ∨ w.count x = 1 ∨ w.count x = 2 ∨ w.count x = 3 := by omega
      rcases cases with e|e|e|e <;> rw [e] at h account <;> omega
    · exact large
  · let p := w.take 9
    let r := w.drop 9
    have plen : p.length = 9 := by simp [p,len]
    have missing : ∃ x : Fin 10, x ∉ p := by
      apply Classical.byContradiction
      intro no
      have sub : finRange 10 ⊆ p := fun a _ => Classical.byContradiction (fun h => no ⟨a,h⟩)
      have := (nodup_finRange 10).length_le_of_subset sub
      simp [plen] at this
    obtain ⟨x,hx⟩ := missing
    have eq : w = p ++ r := (take_append_drop _ _).symm
    have h := projected_bound (transportNine nine x) (front hx (eq ▸ cover))
    have account := length_account x r
    have count : w.count x = r.count x := by rw [eq,count_append,count_eq_zero.mpr hx,Nat.zero_add]
    have total : w.length = p.length + r.length := by rw [eq,length_append]
    exact ⟨x,by omega⟩

/-- Display the five pivot-free gaps of a four-copy word. -/
theorem fourGaps {x : α} {w : List α} (hw : w.count x = 4) :
    ∃ a b c d e : List α, w = a ++ x :: (b ++ x :: (c ++ x :: (d ++ x :: e))) ∧
      x ∉ a ∧ x ∉ b ∧ x ∉ c ∧ x ∉ d ∧ x ∉ e := by
  obtain ⟨gs,t,ew,ht,hg⟩ := decompose x w
  have len : gs.length = 4 := by
    rwa [ew,count_append,(runs_account hg).1,count_eq_zero.mpr ht,Nat.add_zero] at hw
  rcases gs with _|⟨a,gs⟩ <;> simp at len
  rcases gs with _|⟨b,gs⟩ <;> simp at len
  rcases gs with _|⟨c,gs⟩ <;> simp at len
  rcases gs with _|⟨d,gs⟩ <;> simp at len
  subst gs
  exact ⟨a,b,c,d,t,by simpa [runs,append_assoc] using ew, by simpa [ht] using hg⟩

end Supersequence
