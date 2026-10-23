import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! The bit-stream semantics of an increasing matching page.  A true tag
selects a bit.  The selected source and target streams are paired in order;
false-tagged target bits are preserved.  Tags will be repeated over each
row by the native metadata loader. -/
namespace TransposeFollowup.MatchingXorStream
set_option autoImplicit false

abbrev Record := Bool × Bool

def values (xs : List Record) : List Bool := xs.map Prod.snd
def tags (xs : List Record) : List Bool := xs.map Prod.fst
def selected (xs : List Record) : List Bool :=
  xs.filterMap (fun p => if p.1 then some p.2 else none)

def apply (as : List Bool) : List Record → List Bool
  | [] => []
  | (false,b)::bs => b::apply as bs
  | (true,b)::bs => (as.headD false).xor b::apply as.tail bs

@[simp] theorem selected_nil : selected []=[] := rfl
@[simp] theorem selected_false (a : Bool) (xs : List Record) :
    selected ((false,a)::xs)=selected xs := rfl
@[simp] theorem selected_true (a : Bool) (xs : List Record) :
    selected ((true,a)::xs)=a::selected xs := rfl

@[simp] theorem apply_nil (as : List Bool) : apply as []=[] := rfl
@[simp] theorem apply_false (as : List Bool) (b : Bool) (bs : List Record) :
    apply as ((false,b)::bs)=b::apply as bs := rfl
@[simp] theorem apply_true (a b : Bool) (as : List Bool) (bs : List Record) :
    apply (a::as) ((true,b)::bs)=a.xor b::apply as bs := rfl

@[simp] theorem apply_length (as : List Bool) (bs : List Record) :
    (apply as bs).length=bs.length := by
  induction bs generalizing as with
  | nil => rfl
  | cons p bs ih => cases p with | mk t b => cases t <;> simp [apply, ih]

theorem selected_length_le (xs : List Record) : (selected xs).length≤xs.length :=
  List.length_filterMap_le _ _

theorem nil_apply_of_none (ys : List Record) (h : (selected ys).length=0) :
    apply [] ys=values ys := by
  induction ys with
  | nil => rfl
  | cons p ys ih =>
    rcases p with ⟨t,b⟩
    cases t with
    | false => simpa only [selected_false, apply_false, values, List.map_cons] using congrArg (List.cons b) (ih h)
    | true => simp at h

def tagged (tag : Bool) (xs : List Bool) : List Record := xs.map (fun b => (tag,b))

@[simp] theorem values_tagged (tag : Bool) (xs : List Bool) :
    values (tagged tag xs)=xs := by simp [values, tagged]

@[simp] theorem tags_tagged (tag : Bool) (xs : List Bool) :
    tags (tagged tag xs)=List.replicate xs.length tag := by simp [tags, tagged]

@[simp] theorem selected_tagged (tag : Bool) (xs : List Bool) :
    selected (tagged tag xs)=if tag then xs else [] := by
  cases tag <;> induction xs <;> simp_all [tagged, selected]

end TransposeFollowup.MatchingXorStream
