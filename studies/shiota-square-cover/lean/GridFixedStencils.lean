import GridStencils

namespace GridCover.Fixed

def tee : Stencil where
  guards := {(-3, 1), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (0, -2), (0, 1), (1, -2), (1, 2), (1, 3), (2, -2), (3, -1), (3, 1)}
  optional := {(-3, 0), (-2, 0), (0, 0), (0, 2), (0, 3), (2, 0), (3, 0)}
  graph := {((-3, 0), (-2, 0)), ((-2, 0), (0, 0)), ((0, 0), (0, 2)), ((0, 0), (2, 0)), ((0, 2), (0, 3)), ((2, 0), (3, 0))}
  rays := {((1, 0), 0), ((0, 1), 0), ((-1, 0), 0)}

def line : Stencil where
  guards := {(-3, -3), (-3, -2), (-3, -1), (-2, -2), (-1, -2), (-1, 1), (-1, 3), (0, -3), (0, -1), (0, 1), (0, 3), (1, -3), (1, -1), (1, 1), (1, 2), (2, -3), (2, 2), (3, -3), (3, 2), (3, 3)}
  optional := {(-3, 0), (-2, 0), (-1, 0), (0, 0), (1, 0), (2, 0), (3, 0)}
  graph := {((-3, 0), (-2, 0)), ((-2, 0), (-1, 0)), ((-1, 0), (0, 0)), ((0, 0), (1, 0)), ((1, 0), (2, 0)), ((2, 0), (3, 0))}
  rays := {((-1, 0), 0), ((1, 0), 0)}

def corner : Stencil where
  guards := {(-1, 0), (-1, 3), (0, -1), (1, 3), (3, -1), (3, 1)}
  optional := {(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0), (3, 0)}
  graph := {((0, 0), (0, 1)), ((0, 0), (1, 0)), ((0, 1), (0, 2)), ((0, 2), (0, 3)), ((1, 0), (2, 0)), ((2, 0), (3, 0))}
  rays := {((1, 0), 0), ((0, 1), 0)}

def switch : Stencil where
  guards := {(-3, -3), (-3, -1), (-2, -2), (-2, -1), (-1, 1), (-1, 2), (0, -3), (0, 2), (0, 3), (1, 0), (1, 3), (2, -2), (2, 1), (2, 3), (3, -3), (3, -1), (3, 3)}
  optional := {(-3, 0), (-2, 0), (0, -1), (0, 1), (2, 0), (3, 0)}
  graph := {((-3, 0), (-2, 0)), ((-2, 0), (0, 1)), ((0, -1), (0, 1)), ((0, -1), (2, 0)), ((2, 0), (3, 0))}
  rays := {((-1, 0), 0), ((1, 0), 0)}

def end_cap : Stencil where
  guards := {(-1, 2), (0, -2), (0, -1), (0, 1), (1, -1), (1, 1)}
  optional := {(0, 0), (1, 0), (2, 0), (3, 0)}
  graph := {((0, 0), (1, 0)), ((1, 0), (2, 0)), ((2, 0), (3, 0))}
  rays := {((1, 0), 0)}

def switch_corner : Stencil where
  guards := {(-3, -1), (-3, 1), (-2, -1), (0, 1), (1, -2), (1, -1), (1, 1), (2, -1)}
  optional := {(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 2), (0, 3)}
  graph := {((-3, 0), (-2, 0)), ((-2, 0), (-1, 0)), ((-1, 0), (0, 0)), ((0, 0), (0, 2)), ((0, 2), (0, 3))}
  rays := {((-1, 0), 0), ((0, 1), 0)}

theorem tee_data : tee.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tee_raw : ∀ p ∈ box 5 (0, 0), rawCheck tee.roles tee.links p := by decide

theorem tee_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck tee.roles tee.links p :=
  geometric_core_of_checked_collar (r := 3) tee_raw hp

theorem tee_edge {p q : Center} (h : (p, q) ∈ tee.graph) :
    ∃ e ∈ perimeter p, geometricCoverers tee.roles e = {p, q} :=
  Stencil.declared_edge_private tee_data (fun _ hp => tee_geometry hp) h

theorem line_data : line.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem line_raw : ∀ p ∈ box 5 (0, 0), rawCheck line.roles line.links p := by decide

theorem line_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck line.roles line.links p :=
  geometric_core_of_checked_collar (r := 3) line_raw hp

theorem line_edge {p q : Center} (h : (p, q) ∈ line.graph) :
    ∃ e ∈ perimeter p, geometricCoverers line.roles e = {p, q} :=
  Stencil.declared_edge_private line_data (fun _ hp => line_geometry hp) h

theorem corner_data : corner.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem corner_raw : ∀ p ∈ box 5 (0, 0), rawCheck corner.roles corner.links p := by decide

theorem corner_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck corner.roles corner.links p :=
  geometric_core_of_checked_collar (r := 3) corner_raw hp

theorem corner_edge {p q : Center} (h : (p, q) ∈ corner.graph) :
    ∃ e ∈ perimeter p, geometricCoverers corner.roles e = {p, q} :=
  Stencil.declared_edge_private corner_data (fun _ hp => corner_geometry hp) h

theorem switch_data : switch.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem switch_raw : ∀ p ∈ box 5 (0, 0), rawCheck switch.roles switch.links p := by decide

theorem switch_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck switch.roles switch.links p :=
  geometric_core_of_checked_collar (r := 3) switch_raw hp

theorem switch_edge {p q : Center} (h : (p, q) ∈ switch.graph) :
    ∃ e ∈ perimeter p, geometricCoverers switch.roles e = {p, q} :=
  Stencil.declared_edge_private switch_data (fun _ hp => switch_geometry hp) h

theorem end_cap_data : end_cap.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem end_cap_raw : ∀ p ∈ box 5 (0, 0), rawCheck end_cap.roles end_cap.links p := by decide

theorem end_cap_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck end_cap.roles end_cap.links p :=
  geometric_core_of_checked_collar (r := 3) end_cap_raw hp

theorem end_cap_edge {p q : Center} (h : (p, q) ∈ end_cap.graph) :
    ∃ e ∈ perimeter p, geometricCoverers end_cap.roles e = {p, q} :=
  Stencil.declared_edge_private end_cap_data (fun _ hp => end_cap_geometry hp) h

theorem switch_corner_data : switch_corner.dataValid := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem switch_corner_raw : ∀ p ∈ box 5 (0, 0), rawCheck switch_corner.roles switch_corner.links p := by decide

theorem switch_corner_geometry {p : Center} (hp : p ∈ box 3 (0, 0)) :
    geometricCheck switch_corner.roles switch_corner.links p :=
  geometric_core_of_checked_collar (r := 3) switch_corner_raw hp

theorem switch_corner_edge {p q : Center} (h : (p, q) ∈ switch_corner.graph) :
    ∃ e ∈ perimeter p, geometricCoverers switch_corner.roles e = {p, q} :=
  Stencil.declared_edge_private switch_corner_data (fun _ hp => switch_corner_geometry hp) h

end GridCover.Fixed
