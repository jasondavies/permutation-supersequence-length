import Frequency

/-! An analytic exclusion of four copies using only lower-dimensional lengths. -/
namespace Supersequence
open List
variable {α : Type} [DecidableEq α]

def LengthBound (k L : Nat) := ∀ w : List (Fin k), Universal w → L ≤ w.length

private def mass (w A : List α) := (A.map w.count).sum
private def rest (A S : List α) := A.filter (fun a => !S.contains a)

private theorem mass_cons (a : α) (w A : List α) :
    mass (a::w) A = mass w A + A.count a := by
  induction A with
  | nil => simp [mass]
  | cons b A ih =>
    by_cases e : a=b
    · subst b; simp [mass,count_cons] at *; omega
    · simp [mass,count_cons,e,Ne.symm e] at *; omega

private theorem mass_eq {A : List α} (nd : A.Nodup) (w : List α) :
    mass w A = (w.filter A.contains).length := by
  induction w with
  | nil => induction A <;> simp_all [mass]
  | cons a w ih =>
    rw [mass_cons, ih, nd.count]
    by_cases ha : a ∈ A <;> simp [ha]

private theorem mass_le (w : List α) {A : List α} (nd : A.Nodup) :
    mass w A ≤ w.length := by rw [mass_eq nd]; apply length_filter_le

private theorem mass_split {A S : List α} (ha : A.Nodup) (hs : S.Nodup) (sub : S ⊆ A) :
    (S ++ rest A S).Perm A := by
  have nd : (S ++ rest A S).Nodup := by
    refine nodup_append.mpr ⟨hs,ha.sublist filter_sublist,?_⟩
    intro a h b hb e
    simp [rest,←e,h] at hb
  apply perm_iff_count.mpr
  intro a
  rw [nd.count,ha.count]
  by_cases h : a ∈ S
  · simp [rest,h,sub h]
  · simp [rest,h]

private theorem facts {A S : List α} (ha : A.Nodup) (hs : S.Nodup) (sub : S ⊆ A) (w : List α) :
    S.length + (rest A S).length = A.length ∧ mass w S + mass w (rest A S) = mass w A := by
  have hp := mass_split ha hs sub
  refine ⟨by simpa using hp.length_eq, ?_⟩
  have eq : mass w (S ++ rest A S) = mass w A := by
    rw [mass_eq (hp.nodup_iff.mpr ha), mass_eq ha]
    congr 1
    apply filter_congr
    intro a _
    simp [hp.mem_iff]
  simpa [mass] using eq

private theorem mass_upper {w A : List α} {c : Nat} (h : ∀ a ∈ A, w.count a ≤ c) :
    mass w A ≤ A.length*c := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    have ht := ih (fun b hb => h b (.tail _ hb))
    have hh := h a (.head _)
    simp [mass,Nat.succ_mul] at *; omega

private theorem mass_lower {w A : List α} {c : Nat} (h : ∀ a ∈ A, c ≤ w.count a) :
    A.length*c ≤ mass w A := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    have ht := ih (fun b hb => h b (.tail _ hb))
    have hh := h a (.head _)
    simp [mass,Nat.succ_mul] at *; omega

private theorem on_subset {A w : List α} {k L : Nat} (bound : LengthBound k L)
    (hn : A.Nodup) (len : A.length = k) (hk : 0 < k) (cov : Covers (· ∈ A) w) :
    L ≤ mass w A := by
  subst k
  let enc (i : Fin A.length) := A.get i
  let dec (a : α) : Fin A.length := ⟨A.idxOf a % A.length,Nat.mod_lt _ hk⟩
  have inv (i : Fin A.length) : dec (enc i) = i := by
    apply Fin.ext; simp [dec,enc,hn.idxOf_getElem i.val i.isLt,Nat.mod_eq_of_lt i.isLt]
  let old := w.filter A.contains
  have hc : Covers (fun _ => True) (old.map dec) := by
    intro q hq _
    have nd : (q.map enc).Nodup := pairwise_map.mpr (hq.imp (by
      intro a b hab e; exact hab (by simpa only [inv] using congrArg dec e)))
    have mem : ∀ a ∈ q.map enc, a ∈ A := by
      intro a ha; obtain ⟨i,_,rfl⟩ := mem_map.mp ha; exact A.get_mem i
    have he := (cov _ nd mem).filter A.contains
    rw [filter_eq_self.mpr (by simpa using mem)] at he
    have result := he.map dec
    simpa [map_map,Function.comp_def,inv,old] using result
  rw [mass_eq hn]
  simpa [old] using bound _ (universal_iff_covers.mpr hc)

omit [DecidableEq α] in
private theorem largest (f : α → Nat) {A : List α} (ha : A ≠ []) :
    ∃ a ∈ A, ∀ b ∈ A, f b ≤ f a := by
  induction A with
  | nil => contradiction
  | cons a t ih =>
    by_cases ht : t = []
    · subst t; simp
    · obtain ⟨b,hb,hm⟩ := ih ht
      by_cases h : f a ≤ f b
      · exact ⟨b,.tail _ hb,by intro c hc; rcases mem_cons.mp hc with rfl|hh <;> grind⟩
      · exact ⟨a,.head _,by intro c hc; rcases mem_cons.mp hc with rfl|hh <;> grind⟩

/-- Every nonempty universal alphabet has a letter occurring at least its size times. -/
theorem heavyLetter {A w : List α} (nd : A.Nodup) (nonempty : A ≠ [])
    (cov : Covers (· ∈ A) w) : ∃ a ∈ A, A.length ≤ w.count a := by
  obtain ⟨x,hx,maximal⟩ := largest (fun a => w.idxOf a) nonempty
  have xw : x ∈ w := singleton_sublist.mp (cov [x] (by simp) (by simpa using hx))
  obtain ⟨p,t,ew,hp⟩ := eq_append_cons_of_mem xw
  let B := A.erase x
  have bl : B.length = A.length-1 := length_erase_of_mem hx
  by_cases empty : B = []
  · exact ⟨x,hx,by have := count_pos_iff.mpr xw; simp [empty] at bl; omega⟩
  have tail : Covers (· ∈ B) t := by
    intro q hn hq
    have xq : x ∉ q := fun h => nd.not_mem_erase (hq x h)
    have hh := cov (x::q) (by simp [xq,hn]) (by
      intro a ha; rcases mem_cons.mp ha with rfl | h
      · exact hx
      · exact erase_subset (hq a h))
    rw [ew] at hh
    exact cons_sublist_cons.mp (skipGap hp hh)
  obtain ⟨a,ha,freq⟩ := heavyLetter (nd.erase x) empty tail
  have ne : a ≠ x := fun e => nd.not_mem_erase (e ▸ ha)
  have aa : a ∈ A := erase_subset ha
  have ap : a ∈ p := by
    apply Classical.byContradiction
    intro miss
    have h := maximal a aa
    simp [ew,idxOf_append,hp,miss,idxOf_cons,Ne.symm ne] at h; omega
  change B.length ≤ t.count a at freq
  exact ⟨a,aa,by have := count_pos_iff.mpr ap; rw [ew,count_append,count_cons]; omega⟩
termination_by A.length
decreasing_by rw [length_erase_of_mem hx]; have := length_pos_iff.mpr nonempty; omega

def Compatible (A p q : List α) : Prop :=
  ∀ S : List α, S ⊆ A → Covers (· ∈ S) p ∨ Covers (· ∈ rest A S) q

omit [DecidableEq α] in
private theorem mono {P Q : α → Prop} {w : List α} (h : Covers P w)
    (sub : ∀ a, Q a → P a) : Covers Q w :=
  fun r hn mem => h r hn (fun a ha => sub a (mem a ha))

private theorem positiveSide {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (cutOK : Compatible A p q) (f8 : LengthBound 8 52) (short : q.length < 52) :
    ∀ a ∈ A, a ∈ p := by
  have totalQ := mass_le q ha
  intro a mem
  apply Classical.byContradiction; intro missing
  have sub : [a] ⊆ A := by simpa using mem
  rcases cutOK [a] sub with left | right
  · exact missing (singleton_sublist.mp (left [a] (by simp) (by simp)))
  · obtain ⟨len,eq⟩ := facts ha (by simp : [a].Nodup) sub q
    have h := on_subset f8 (ha.sublist filter_sublist)
      (A := rest A [a]) (by simp at len; omega) (by decide) right
    omega

private def onesIn (p A : List α) := A.filter (fun a => p.count a == 1)

private theorem supply {A p : List α} (ha : A.Nodup) (n : A.length = 9)
    (all : ∀ a ∈ A, a ∈ p) : 18 ≤ p.length + (onesIn p A).length := by
  have totalP := mass_le p ha
  let singles := A.filter (fun a => p.count a == 1)
  have ns : singles.Nodup := ha.sublist filter_sublist
  have subS : singles ⊆ A := filter_sublist.subset
  have single (a) (h : a ∈ singles) : p.count a = 1 := by simpa [singles] using (mem_filter.mp h).2
  change 18 ≤ p.length + singles.length
  obtain ⟨len,eq⟩ := facts ha ns subS p
  have ones := mass_lower (c := 1) (A := singles) (w := p) (by grind)
  have twos := mass_lower (c := 2) (A := rest A singles) (w := p) (by
    intro a mem
    have ⟨aa,notin⟩ := mem_filter.mp mem
    have pos := count_pos_iff.mpr (all a aa)
    have neq : p.count a ≠ 1 := by
      intro one; have ins : a ∈ singles := by simp [singles,aa,one]
      simp [ins] at notin
    omega)
  omega

private theorem coverSix {A p q S : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 12) (cutOK : Compatible A p q) (f3 : LengthBound 3 7)
    (ndS : S.Nodup) (lenS : S.length = 6) (subSA : S ⊆ A)
    (ones : ∀ a ∈ S, p.count a = 1) : Covers (· ∈ S) q := by
  have totalP := mass_le p ha
  have bounds := facts ha ndS subSA p
  have comp3 : (rest A S).length = 3 := by omega
  have compSub : rest A S ⊆ A := filter_sublist.subset
  rcases cutOK (rest A S) compSub with left | right
  · have three := on_subset f3 (ha.sublist filter_sublist) comp3 (by decide) left
    change 7 ≤ mass p (rest A S) at three
    have six := mass_lower (w := p) (A := S) (c := 1) (by grind)
    omega
  · apply mono right
    intro a mem
    simp [rest,mem,subSA mem]

private theorem pairBudget {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (cutOK : Compatible A p q) (f2 : LengthBound 2 3) (f7 : LengthBound 7 39)
    {a b : α} (aa : a ∈ A) (bb : b ∈ A) (ne : a ≠ b)
    (oneA : p.count a = 1) (oneB : p.count b = 1) : q.count a + q.count b + 39 ≤ q.length := by
  have totalQ := mass_le q ha
  have nd : [a,b].Nodup := by simp [ne]
  have sub : [a,b] ⊆ A := by simpa using And.intro aa bb
  obtain ⟨len,eq⟩ := facts ha nd sub q
  rcases cutOK [a,b] sub with left | right
  · have h := on_subset f2 nd rfl (by decide) left
    simp [mass,oneA,oneB] at h
  · have h := on_subset f7 (ha.sublist filter_sublist) (A := rest A [a,b])
        (by simp at len; omega) (by decide) right
    simp [mass] at eq totalQ
    change 39 ≤ (map (fun z => q.count z) (rest A [a,b])).sum at h
    omega

/-- A complementary cut on nine old letters with first side of length at most
12 requires at least 50 positions on the other side. -/
theorem outerCutLength {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 12) (cutOK : Compatible A p q)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) : 50 ≤ q.length := by
  apply Classical.byContradiction
  intro short
  have all := positiveSide ha n cutOK f8 (by omega)
  let singles := onesIn p A
  have ns : singles.Nodup := ha.sublist filter_sublist
  have subS : singles ⊆ A := filter_sublist.subset
  have single (a) (h : a ∈ singles) : p.count a = 1 := by simpa [singles,onesIn] using (mem_filter.mp h).2
  have enough : 6 ≤ singles.length := by have := supply ha n all; change 6 ≤ (onesIn p A).length; omega
  let S := singles.take 6
  have lenS : S.length = 6 := by simp [S,length_take,Nat.min_eq_left enough]
  have ndS : S.Nodup := ns.sublist (take_sublist ..)
  have subSA : S ⊆ A := fun _ h => subS (mem_of_mem_take h)
  have ones (a) (h : a ∈ S) := single a (mem_of_mem_take h)
  have covered := coverSix ha n small cutOK f3 ndS lenS subSA ones
  have twentyEight := on_subset f6 ndS lenS (by decide) covered
  obtain ⟨a,haS,heavy⟩ := heavyLetter ndS (by intro e; simp [e] at lenS) covered
  let R := rest S [a]
  have pairbound (b : α) (hb : b ∈ R) : q.count a + q.count b ≤ 10 := by
    have ⟨hbS,neq⟩ := mem_filter.mp hb
    have ne : a ≠ b := by intro e; simp [← e] at neq
    have := pairBudget ha n cutOK f2 f7 (subSA haS) (subSA hbS) ne (ones a haS) (ones b hbS)
    omega
  obtain ⟨lenR,eqR⟩ := facts ndS (by simp : [a].Nodup) (by simpa using haS : [a] ⊆ S) q
  have five : R.length = 5 := by change 1 + R.length = S.length at lenR; omega
  have someR : ∃ b, b ∈ R := by cases e : R with
                                  | nil => simp [e] at five
                                  | cons b t => exact ⟨b,by simp⟩
  obtain ⟨b,hb⟩ := someR
  have lim := pairbound b hb
  have sum := mass_upper (A := R) (w := q) (c := 10 - q.count a)
    (by intro c hc; have := pairbound c hc; omega)
  change mass q [a] + mass q R = mass q S at eqR
  rw [show mass q [a] = q.count a by simp [mass]] at eqR
  rw [five] at sum
  omega


/-- With one fewer position on the short side, every six of seven
singletons must be covered on the opposite side. -/
theorem outerCutEleven {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 11) (cutOK : Compatible A p q)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) : 51 ≤ q.length := by
  apply Classical.byContradiction
  intro short
  have all := positiveSide ha n cutOK f8 (by omega)
  let pool := onesIn p A
  have nd : pool.Nodup := ha.sublist filter_sublist
  have sub : pool ⊆ A := filter_sublist.subset
  have one {a} (mem : a ∈ pool) : p.count a = 1 := by simpa [pool,onesIn] using (mem_filter.mp mem).2
  have seven : 7 ≤ pool.length := by have := supply ha n all; change 7 ≤ (onesIn p A).length; omega
  have getHeavy (T : List α) (ht : T.Nodup) (incl : T ⊆ pool) (sz : 6 ≤ T.length) :
      ∃ a ∈ T, 6 ≤ q.count a := by
    let S := T.take 6
    have len : S.length = 6 := by simp [S,length_take,Nat.min_eq_left sz]
    have ns : S.Nodup := ht.sublist (take_sublist ..)
    have inPool {a} (h : a ∈ S) := incl (mem_of_mem_take h)
    have cov := coverSix ha n (by omega) cutOK f3 ns len
      (fun z h => sub (inPool h)) (fun z h => one (inPool h))
    obtain ⟨a,mem,big⟩ := heavyLetter ns (by intro e; simp [e] at len) cov
    exact ⟨a,mem_of_mem_take mem,by omega⟩
  obtain ⟨a,haP,bigA⟩ := getHeavy pool nd (fun _ h => h) (by omega)
  obtain ⟨b,hbP,bigB⟩ := getHeavy (pool.erase a) (nd.erase a) erase_subset
    (by rw [length_erase_of_mem haP]; omega)
  have ne : a ≠ b := fun e => nd.not_mem_erase (e ▸ hbP)
  have bm := erase_subset hbP
  have := pairBudget ha n cutOK f2 f7 (sub haP) (sub bm) ne (one haP) (one bm)
  omega

private theorem compatible_swap {A p q : List α} (h : Compatible A p q) : Compatible A q p := by
  intro S sub
  rcases h (rest A S) filter_sublist.subset with left | right
  · exact .inr left
  · exact .inl (mono right (by intro a mem; simp [rest,mem,sub mem]))

private theorem keep {x : α} {P : α → Prop} {w : List α} (h : Covers P w)
    (free : ∀ a, P a → a ≠ x) : Covers P (project x w) := by
  intro q hn hq
  have he := (h _ hn hq).filter (· != x)
  rwa [show q.filter (· != x) = q from project_free (fun m => free x (hq x m) rfl)] at he

private theorem projectedCut {x : Fin 10} {l g r : List (Fin 10)}
    (hg : x ∉ g) (hw : Covers (fun _ => True) (l ++ (g ++ r))) :
    Compatible ((finRange 10).erase x) (project x l) (project x r) := by
  intro S sub
  have ha (a : Fin 10) : a ∈ (finRange 10).erase x ↔ a ≠ x := by
    by_cases e : a=x
    · subst a; simp [(nodup_finRange 10).not_mem_erase]
    · simp [mem_erase_of_ne e,mem_finRange,e]
  rcases complementaryCut hg hw (· ∈ S) with left | right
  · exact .inl (mono (keep left (fun a h => h.1)) (fun a m => ⟨(ha a).mp (sub m),m⟩))
  · exact .inr (mono (keep right (fun a h => h.1)) (by
      intro a m; simpa [rest,ha] using m))

/-- Four occurrences are impossible at length 82. The hypotheses are the
classical small-alphabet lower bounds and the separate nine-letter result. -/
theorem noFour {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66) :
    ∀ x, w.count x ≠ 4 := by
  intro x mult
  obtain ⟨a,b,c,d,e,eq,ha,hb,hc,hd,he⟩ := fourGaps mult
  have cover := universal_iff_covers.mp hw
  let A := (finRange 10).erase x
  have nd : A.Nodup := (nodup_finRange 10).erase x
  have nine : A.length = 9 := by simp [A,length_erase_of_mem (mem_finRange x)]
  have low := transportNine f9 x
  have total : a.length + b.length + c.length + d.length + e.length = 78 := by
    simp [eq] at len; omega
  have head := front (x := x) ha (eq ▸ cover)
  have left := projected_bound low head
  simp only [project_cons_self,project_append,project_free hb,project_free hc,
    project_free hd,project_free he,length_append] at left
  have eq' : w = (a ++ x :: (b ++ x :: (c ++ x :: (d ++ [x])))) ++ e := by simp [eq,append_assoc]
  have right := projected_bound low (back he (eq' ▸ cover))
  simp only [project_cons_self,project_append,project_free ha,project_free hb,project_free hc,
    project_free hd,length_append,show project x [x] = [] by simp [project],length_nil] at right
  have h₁ := projectedCut hb (l := a ++ [x]) (r := x :: (c ++ x :: (d ++ x :: e)))
    (x := x) (by simpa only [append_assoc,singleton_append] using eq ▸ cover)
  have h₂ := projectedCut hd (l := a ++ x :: (b ++ x :: (c ++ [x]))) (r := x :: e)
    (x := x) (by simpa [append_assoc] using eq ▸ cover)
  have emp : project x [x] = [] := by simp [project]
  simp only [project_append,project_cons_self,project_free ha,project_free hb,project_free hc,
    project_free hd,project_free he,emp,append_nil] at h₁ h₂
  have fifty₁ := outerCutLength nd nine (by omega : a.length ≤ 12) h₁ f2 f3 f6 f7 f8
  have fifty₂ := outerCutLength nd nine (by omega : e.length ≤ 12) (compatible_swap h₂) f2 f3 f6 f7 f8
  simp only [length_append] at fifty₁ fifty₂
  have gap := bridge (x := x) hc (alphabet := A)
    (fun i ne => (mem_erase_of_ne ne).mpr (mem_finRange i))
    (l := a ++ x :: (b ++ [x])) (r := x :: (d ++ x :: e))
    (by simpa [append_assoc] using eq ▸ cover)
  have lower := projected_bound low gap
  have hA : x ∉ A := (nodup_finRange 10).not_mem_erase
  simp only [project_append,project_cons_self,project_free ha,project_free hb,
    project_free hd,project_free he,project_free hA,emp,append_nil,length_append,nine] at lower
  omega

/-- The remaining computational branches exhaust the possible minimum frequencies. -/
theorem remainingFrequencies {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66)
    (x : Fin 10) (least : ∀ a, w.count x ≤ w.count a) :
    w.count x = 5 ∨ w.count x = 6 ∨ w.count x = 7 := by
  obtain ⟨lower,y,hy⟩ := frequencySplit f9 hw len
  have four := noFour hw len f2 f3 f6 f7 f8 f9 x
  have := least y
  have := lower x
  omega

end Supersequence
