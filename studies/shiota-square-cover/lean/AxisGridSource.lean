import Lean.Elab.Tactic.Omega

namespace AxisGridSource

abbrev Point := Int × Int

/-- The two orientations of an undirected, nondegenerate axis-aligned segment. -/
inductive Axis where
  | east
  | north
  deriving DecidableEq, Repr

def span (a b p : Point) : Prop :=
  a.1 ≤ p.1 ∧ p.1 ≤ b.1 ∧ a.2 ≤ p.2 ∧ p.2 ≤ b.2

def straight (a b : Point) : Prop :=
  (a.1 < b.1 ∧ a.2 = b.2) ∨ (a.1 = b.1 ∧ a.2 < b.2)

def double (p : Point) : Point := (2 * p.1, 2 * p.2)
def lower (p : Point) : Point := (p.1 / 2, p.2 / 2)
def upper (p : Point) : Point := ((p.1 + 1) / 2, (p.2 + 1) / 2)

def axis (a b : Point) : Axis := if a.2 = b.2 then .east else .north

def advance (p : Point) (d : Axis) (i : Int) : Point :=
  match d with
  | .east => (p.1+i,p.2)
  | .north => (p.1,p.2+i)

def length (a b : Point) : Nat := ((b.1-a.1) + (b.2-a.2)).toNat

def site (a b : Point) (i : Nat) : Point := advance (double a) (axis a b) i

def adjacent (p q : Point) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
  (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨ (p.1 = q.1 ∧ q.2 + 1 = p.2)

theorem double_injective : Function.Injective double := by
  intro p q hpq
  have hx := congrArg Prod.fst hpq
  have hy := congrArg Prod.snd hpq
  simp [double] at hx hy
  exact Prod.ext (by omega) (by omega)

theorem span_double_iff (a b p : Point) :
    span (double a) (double b) (double p) ↔ span a b p := by
  simp only [span, double]
  omega

theorem span_rounding {a b p : Point} (h : span (double a) (double b) p) :
    span a b (lower p) ∧ span a b (upper p) := by
  simp only [span, double, lower, upper] at *
  omega

theorem exact_rounding {p : Point} (h : lower p = upper p) :
    double (lower p) = p := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [lower, upper] at hx hy
  apply Prod.ext <;> simp only [double, lower] <;> omega

theorem length_pos {a b : Point} (h : straight a b) : 0 < length a b := by
  simp only [straight, length] at *
  omega

theorem length_le_of_box {a b : Point} {n : Nat} (h : straight a b)
    (ha : 1 ≤ a.1 ∧ a.1 ≤ (n : Int) ∧ 1 ≤ a.2 ∧ a.2 ≤ (n : Int))
    (hb : 1 ≤ b.1 ∧ b.1 ≤ (n : Int) ∧ 1 ≤ b.2 ∧ b.2 ≤ (n : Int)) :
    length a b ≤ n - 1 := by
  simp only [straight, length] at *
  omega

theorem site_zero (a b : Point) : site a b 0 = double a := by
  unfold site
  cases axis a b <;> simp [advance]

theorem site_succ (a b : Point) (i : Nat) :
    site a b (i+1) = advance (site a b i) (axis a b) 1 := by
  unfold site
  cases axis a b <;> apply Prod.ext <;> simp [advance] <;> omega

theorem site_last {a b : Point} (h : straight a b) :
    site a b (2 * length a b) = double b := by
  rcases h with h | h
  · simp only [site, axis, ite_eq_left h.2, advance, double, length]
    apply Prod.ext <;> change _ = _ <;> omega
  · have hn : a.2 ≠ b.2 := by omega
    simp only [site, axis, ite_eq_right hn, advance, double, length]
    apply Prod.ext <;> change _ = _ <;> omega

theorem site_injective (a b : Point) : Function.Injective (site a b) := by
  intro i j h
  unfold site at h
  cases hd : axis a b
  · have hx := congrArg Prod.fst h
    simp [hd, advance] at hx
    omega
  · have hy := congrArg Prod.snd h
    simp [hd, advance] at hy
    omega

theorem site_span {a b : Point} {i : Nat} (h : straight a b)
    (hi : i ≤ 2 * length a b) : span (double a) (double b) (site a b i) := by
  rcases h with h | h
  · simp only [span, site, axis, ite_eq_left h.2, advance, double, length] at *
    omega
  · have hn : a.2 ≠ b.2 := by omega
    simp only [span, site, axis, ite_eq_right hn, advance, double, length] at *
    omega

theorem adjacent_symm {p q : Point} (h : adjacent p q) : adjacent q p := by
  simp only [adjacent] at *
  omega

theorem sites_adjacent_iff (a b : Point) (i j : Nat) :
    adjacent (site a b i) (site a b j) ↔ i + 1 = j ∨ j + 1 = i := by
  unfold site
  cases axis a b <;> simp [advance, adjacent] <;> omega

/-- Either endpoint of a fine-grid unit step, if it has the odd moving coordinate,
belongs to a doubled span only when its even neighbor belongs as well. -/
theorem adjacent_spans_touch {a b c d p q : Point}
    (hp : span (double a) (double b) p) (hq : span (double c) (double d) q)
    (h : adjacent p q) :
    span (double a) (double b) q ∨ span (double c) (double d) p := by
  simp only [span, double, adjacent] at *
  omega

theorem hubs_not_adjacent (p q : Point) : ¬ adjacent (double p) (double q) := by
  simp only [adjacent, double]
  omega

def Ends (v : V) (e : V × V) : Prop := v = e.1 ∨ v = e.2

theorem edge_order_of_distinct_ends {e : V × V} {v w : V}
    (hv : Ends v e) (hw : Ends w e) (ne : v ≠ w) :
    e = (v,w) ∨ e = (w,v) := by
  rcases e with ⟨a,b⟩
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact (ne (hv.trans hw.symm)).elim
  · exact Or.inl (Prod.ext hv.symm hw.symm)
  · exact Or.inr (Prod.ext hw.symm hv.symm)
  · exact (ne (hv.trans hw.symm)).elim

/-- Integer bendless plane drawing of a simple graph. Edge order is geometric. -/
structure Drawing (V : Type) where
  vertices : List V
  edges : List (V × V)
  coordinate : V → Point
  coordinate_injective : Function.Injective coordinate
  edge_endpoints : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices
  edge_straight : ∀ e ∈ edges, straight (coordinate e.1) (coordinate e.2)
  vertex_clear : ∀ e ∈ edges, ∀ v ∈ vertices,
    span (coordinate e.1) (coordinate e.2) (coordinate v) → Ends v e
  shared_endpoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
    ∀ p, span (coordinate e.1) (coordinate e.2) p →
      span (coordinate f.1) (coordinate f.2) p →
      ∃ v, Ends v e ∧ Ends v f ∧ coordinate v = p
  coordinates_bounded : ∀ v ∈ vertices,
    1 ≤ (coordinate v).1 ∧ (coordinate v).1 ≤ (vertices.length : Int) ∧
    1 ≤ (coordinate v).2 ∧ (coordinate v).2 ≤ (vertices.length : Int)

namespace Drawing
variable {V : Type} (D : Drawing V)

def hub (v : V) : Point := double (D.coordinate v)
def axis (e : V × V) : Axis := AxisGridSource.axis (D.coordinate e.1) (D.coordinate e.2)
def length (e : V × V) : Nat := AxisGridSource.length (D.coordinate e.1) (D.coordinate e.2)
def site (e : V × V) (i : Nat) : Point :=
  AxisGridSource.site (D.coordinate e.1) (D.coordinate e.2) i
def inside (e : V × V) : List Point :=
  (List.range (2 * D.length e - 1)).map (fun i => D.site e (i+1))
def occupied : List Point := D.vertices.map D.hub ++ D.edges.flatMap D.inside
def fineSpan (e : V × V) (p : Point) : Prop := span (D.hub e.1) (D.hub e.2) p

theorem hub_injective : Function.Injective D.hub :=
  fun _ _ h => D.coordinate_injective (double_injective h)

theorem length_pos {e : V × V} (he : e ∈ D.edges) : 0 < D.length e :=
  AxisGridSource.length_pos (D.edge_straight e he)

theorem length_bound {e : V × V} (he : e ∈ D.edges) : D.length e ≤ D.vertices.length - 1 :=
  length_le_of_box (D.edge_straight e he)
    (D.coordinates_bounded e.1 (D.edge_endpoints e he).1)
    (D.coordinates_bounded e.2 (D.edge_endpoints e he).2)

theorem site_zero (e : V × V) : D.site e 0 = D.hub e.1 := AxisGridSource.site_zero _ _

theorem site_succ (e : V × V) (i : Nat) :
    D.site e (i+1) = advance (D.site e i) (D.axis e) 1 :=
  AxisGridSource.site_succ _ _ _

theorem site_last {e : V × V} (he : e ∈ D.edges) :
    D.site e (2 * D.length e) = D.hub e.2 :=
  AxisGridSource.site_last (D.edge_straight e he)

theorem site_injective (e : V × V) : Function.Injective (D.site e) :=
  AxisGridSource.site_injective _ _

theorem site_span {e : V × V} (he : e ∈ D.edges) {i : Nat}
    (hi : i ≤ 2 * D.length e) : D.fineSpan e (D.site e i) :=
  AxisGridSource.site_span (D.edge_straight e he) hi

theorem length_inside (e : V × V) : (D.inside e).length = 2 * D.length e - 1 := by
  simp [inside]

theorem mem_inside {e : V × V} {p : Point} :
    p ∈ D.inside e ↔ ∃ i, 0 < i ∧ i < 2 * D.length e ∧ D.site e i = p := by
  simp only [inside, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i+1, by omega, by omega, h⟩
  · rintro ⟨i, hi, hil, h⟩
    refine ⟨i-1, by omega, ?_⟩
    have h' : i - 1 + 1 = i := by omega
    rw [h', h]

theorem inside_nodup (e : V × V) : (D.inside e).Nodup := by
  unfold inside List.Nodup
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp (l := List.range (2 * D.length e - 1)) _
    List.nodup_range
  intro i j h h'
  have := D.site_injective e h'
  omega

theorem adjacent_sites_iff (e : V × V) (i j : Nat) :
    adjacent (D.site e i) (D.site e j) ↔ i + 1 = j ∨ j + 1 = i :=
  sites_adjacent_iff _ _ _ _

theorem site_mem_occupied {e : V × V} (he : e ∈ D.edges) {i : Nat}
    (hi : i ≤ 2 * D.length e) : D.site e i ∈ D.occupied := by
  unfold occupied
  apply List.mem_append.mpr
  rcases Nat.eq_zero_or_pos i with rfl | hpositive
  · left
    exact List.mem_map.mpr ⟨e.1, (D.edge_endpoints e he).1, (D.site_zero e).symm⟩
  by_cases hend : i = 2 * D.length e
  · left
    exact List.mem_map.mpr ⟨e.2, (D.edge_endpoints e he).2, hend ▸ (D.site_last he).symm⟩
  · right
    apply List.mem_flatMap.mpr
    exact ⟨e, he, D.mem_inside.mpr ⟨i, hpositive, by omega, rfl⟩⟩

theorem shared_unique {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    (hef : e ≠ f) {p q : Point}
    (hep : span (D.coordinate e.1) (D.coordinate e.2) p)
    (hfp : span (D.coordinate f.1) (D.coordinate f.2) p)
    (heq : span (D.coordinate e.1) (D.coordinate e.2) q)
    (hfq : span (D.coordinate f.1) (D.coordinate f.2) q) : p = q := by
  obtain ⟨v,hve,hvf,hvp⟩ := D.shared_endpoint e he f hf hef p hep hfp
  obtain ⟨w,hwe,hwf,hwq⟩ := D.shared_endpoint e he f hf hef q heq hfq
  apply Classical.byContradiction
  intro hne
  have hdiff : v ≠ w := by
    intro h
    exact hne (hvp.symm.trans ((congrArg D.coordinate h).trans hwq))
  have es := D.edge_straight e he
  have fs := D.edge_straight f hf
  rcases edge_order_of_distinct_ends hve hwe hdiff with he' | he'
  · rcases edge_order_of_distinct_ends hvf hwf hdiff with hf' | hf'
    · exact hef (he'.trans hf'.symm)
    · rw [he'] at es
      rw [hf'] at fs
      simp only [straight] at es fs
      omega
  · rcases edge_order_of_distinct_ends hvf hwf hdiff with hf' | hf'
    · rw [he'] at es
      rw [hf'] at fs
      simp only [straight] at es fs
      omega
    · exact hef (he'.trans hf'.symm)

theorem touching_edges {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    (hef : e ≠ f) {p : Point} (hp : D.fineSpan e p) (hq : D.fineSpan f p) :
    ∃ v, Ends v e ∧ Ends v f ∧ D.hub v = p := by
  have h₁ := span_rounding hp
  have h₂ := span_rounding hq
  have hx := D.shared_unique he hf hef h₁.1 h₂.1 h₁.2 h₂.2
  obtain ⟨v, hv, hw, hp⟩ := D.shared_endpoint e he f hf hef (lower p) h₁.1 h₂.1
  exact ⟨v, hv, hw, by rw [hub, hp]; exact exact_rounding hx⟩

theorem touching_vertex {e : V × V} (he : e ∈ D.edges)
    {v : V} (hv : v ∈ D.vertices) (h : D.fineSpan e (D.hub v)) : Ends v e :=
  D.vertex_clear e he v hv ((span_double_iff _ _ _).mp h)

theorem site_ne_ends {e : V × V} (he : e ∈ D.edges) {i : Nat}
    (hi : 0 < i) (hil : i < 2 * D.length e) {v : V} (h : Ends v e) :
    D.site e i ≠ D.hub v := by
  intro hv
  rcases h with rfl | rfl
  · have h := D.site_injective e (hv.trans (D.site_zero e).symm)
    omega
  · have h := D.site_injective e (hv.trans (D.site_last he).symm)
    omega

theorem inside_clear_hub {e : V × V} (he : e ∈ D.edges)
    {v : V} (hv : v ∈ D.vertices) : D.hub v ∉ D.inside e := by
  intro hm
  obtain ⟨i, hi, hil, h⟩ := D.mem_inside.mp hm
  have hes : D.fineSpan e (D.hub v) := h ▸ D.site_span he (Nat.le_of_lt hil)
  exact D.site_ne_ends he hi hil (D.touching_vertex he hv hes) h

theorem inside_disjoint {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    (hef : e ≠ f) {p : Point} (hp : p ∈ D.inside e) (hq : p ∈ D.inside f) : False := by
  obtain ⟨i, hi, hil, rfl⟩ := D.mem_inside.mp hp
  obtain ⟨j, _, hjl, hq⟩ := D.mem_inside.mp hq
  obtain ⟨v, hv, _, h⟩ := D.touching_edges he hf hef
    (D.site_span he (Nat.le_of_lt hil)) (hq ▸ D.site_span hf (Nat.le_of_lt hjl))
  exact D.site_ne_ends he hi hil hv h.symm

theorem inside_not_adjacent_between_edges {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    (hef : e ≠ f) {p q : Point} (hp : p ∈ D.inside e) (hq : q ∈ D.inside f) :
    ¬ adjacent p q := by
  intro h
  obtain ⟨i, hi, hil, hp⟩ := D.mem_inside.mp hp
  obtain ⟨j, hj, hjl, hq⟩ := D.mem_inside.mp hq
  have hps : D.fineSpan e p := hp ▸ D.site_span he (Nat.le_of_lt hil)
  have hqs : D.fineSpan f q := hq ▸ D.site_span hf (Nat.le_of_lt hjl)
  rcases adjacent_spans_touch hps hqs h with hqe | hpf
  · obtain ⟨v, _, hv, h⟩ := D.touching_edges he hf hef hqe hqs
    exact D.site_ne_ends hf hj hjl hv (hq.trans h.symm)
  · obtain ⟨v, hv, _, h⟩ := D.touching_edges he hf hef hps hpf
    exact D.site_ne_ends he hi hil hv (hp.trans h.symm)

theorem adjacent_hub_iff {e : V × V} (he : e ∈ D.edges)
    {v : V} (hv : v ∈ D.vertices) {i : Nat}
    (hi : 0 < i) (hil : i < 2 * D.length e) :
    adjacent (D.hub v) (D.site e i) ↔
    (v = e.1 ∧ i = 1) ∨ (v = e.2 ∧ i + 1 = 2 * D.length e) := by
  constructor
  · intro h
    have hs := D.site_span he (Nat.le_of_lt hil)
    have hvspan : span (double (D.coordinate v)) (double (D.coordinate v)) (D.hub v) := by
      simp [span,hub]
    have htouch := adjacent_spans_touch hvspan hs h
    have hve : D.fineSpan e (D.hub v) := by
      rcases htouch with h' | h'
      · have heq : D.site e i = D.hub v := by
          simp only [span, hub] at h' ⊢
          obtain ⟨h1,h2,h3,h4⟩ := h'
          exact Prod.ext (Int.le_antisymm h2 h1) (Int.le_antisymm h4 h3)
        exact heq ▸ hs
      · exact h'
    rcases D.touching_vertex he hv hve with rfl | rfl
    · rw [← D.site_zero e, D.adjacent_sites_iff] at h
      left
      exact ⟨rfl, by omega⟩
    · rw [← D.site_last he, D.adjacent_sites_iff] at h
      right
      exact ⟨rfl, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, h⟩)
    · rw [← D.site_zero e]
      exact (sites_adjacent_iff _ _ _ _).mpr (Or.inl rfl)
    · rw [← D.site_last he]
      exact (sites_adjacent_iff _ _ _ _).mpr (Or.inr h)

theorem occupied_cases {p : Point} (hp : p ∈ D.occupied) :
    (∃ v ∈ D.vertices, D.hub v = p) ∨
      ∃ e ∈ D.edges, ∃ i, 0 < i ∧ i < 2 * D.length e ∧ D.site e i = p := by
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inl (List.mem_map.mp hp)
  · obtain ⟨e,he,h⟩ := List.mem_flatMap.mp hp
    exact Or.inr ⟨e,he,D.mem_inside.mp h⟩

/-- Every unit adjacency of occupied sites belongs to one specified source path. -/
theorem occupied_adjacent_iff {p q : Point} (hp : p ∈ D.occupied) (hq : q ∈ D.occupied) :
    adjacent p q ↔
      ∃ e ∈ D.edges, ∃ i < 2 * D.length e,
        (p = D.site e i ∧ q = D.site e (i+1)) ∨
        (q = D.site e i ∧ p = D.site e (i+1)) := by
  constructor
  · intro hadj
    rcases D.occupied_cases hp with ⟨v,hv,rfl⟩ | ⟨e,he,i,hi,hiL,rfl⟩
    · rcases D.occupied_cases hq with ⟨w,_,rfl⟩ | ⟨f,hf,j,hj,hjL,rfl⟩
      · exact (hubs_not_adjacent _ _ hadj).elim
      · rcases (D.adjacent_hub_iff hf hv hj hjL).mp hadj with ⟨rfl,rfl⟩ | ⟨rfl,hjlast⟩
        · exact ⟨f,hf,0,by omega,Or.inl ⟨(D.site_zero f).symm,rfl⟩⟩
        · exact ⟨f,hf,j,hjL,Or.inr ⟨rfl,by rw [hjlast,D.site_last hf]⟩⟩
    · rcases D.occupied_cases hq with ⟨w,hw,rfl⟩ | ⟨f,hf,j,hj,hjL,rfl⟩
      · rcases (D.adjacent_hub_iff he hw hi hiL).mp (adjacent_symm hadj) with
          ⟨rfl,rfl⟩ | ⟨rfl,hilast⟩
        · exact ⟨e,he,0,by omega,Or.inr ⟨(D.site_zero e).symm,rfl⟩⟩
        · exact ⟨e,he,i,hiL,Or.inl ⟨rfl,by rw [hilast,D.site_last he]⟩⟩
      · by_cases ef : e = f
        · subst f
          rcases (D.adjacent_sites_iff e i j).mp hadj with h | h
          · exact ⟨e,he,i,hiL,Or.inl ⟨rfl,by rw [h]⟩⟩
          · exact ⟨e,he,j,hjL,Or.inr ⟨rfl,by rw [h]⟩⟩
        · exact (D.inside_not_adjacent_between_edges he hf ef
            (D.mem_inside.mpr ⟨i,hi,hiL,rfl⟩)
            (D.mem_inside.mpr ⟨j,hj,hjL,rfl⟩) hadj).elim
  · rintro ⟨e,_,i,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact (D.adjacent_sites_iff e i (i+1)).mpr (Or.inl rfl)
    · exact (D.adjacent_sites_iff e (i+1) i).mpr (Or.inr rfl)

def dedicated (e : V × V) : Point := D.site e 1

theorem dedicated_inside {e : V × V} (he : e ∈ D.edges) :
    D.dedicated e ∈ D.inside e := by
  have := D.length_pos he
  exact D.mem_inside.mpr ⟨1, by omega, by omega, rfl⟩

theorem dedicated_index (e : V × V) (i : Nat) : D.site e i = D.dedicated e ↔ i = 1 := by
  exact ⟨fun h => D.site_injective e h, fun h => h ▸ rfl⟩

def switch (teeCount : Nat) (e : V × V) (p : Point) : Prop :=
  teeCount % 2 = 0 ∧ p = D.dedicated e

theorem switch_exists_unique {e : V × V} (he : e ∈ D.edges) {teeCount : Nat}
    (h : teeCount % 2 = 0) :
    ∃ p, p ∈ D.inside e ∧ D.switch teeCount e p ∧
      ∀ q, D.switch teeCount e q → q = p :=
  ⟨D.dedicated e, D.dedicated_inside he, ⟨h,rfl⟩, fun _ hq => hq.2⟩

theorem no_switch_of_odd (e : V × V) {teeCount : Nat} (h : teeCount % 2 = 1)
    (p : Point) : ¬ D.switch teeCount e p := by
  unfold switch
  omega

theorem dedicated_disjoint {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    (hef : e ≠ f) : D.dedicated e ≠ D.dedicated f := by
  intro h
  exact D.inside_disjoint he hf hef (D.dedicated_inside he)
    (h.symm ▸ D.dedicated_inside hf)

theorem internal_count_bound (e : V × V) (he : e ∈ D.edges) :
    (D.inside e).length ≤ 2 * D.vertices.length := by
  rw [D.length_inside e]
  have h := D.length_bound he
  omega

theorem routes_size_bound :
    (D.edges.flatMap D.inside).length ≤ D.edges.length * (2 * D.vertices.length) := by
  generalize hes : D.edges = es
  have he : ∀ e ∈ es, (D.inside e).length ≤ 2 * D.vertices.length := by
    intro e h
    exact D.internal_count_bound e (hes ▸ h)
  clear hes
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    have h1 := he e List.mem_cons_self
    have h2 := ih (fun f hf => he f (List.mem_cons_of_mem _ hf))
    omega

theorem occupied_size_bound :
    D.occupied.length ≤ D.vertices.length + D.edges.length * (2 * D.vertices.length) := by
  simpa [occupied] using D.routes_size_bound

end Drawing
end AxisGridSource
