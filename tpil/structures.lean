structure point (α : Type) :=
mk :: (x : α) (y : α)

#print point
#print prefix point


def point.smul (n : ℕ) (p : point ℕ) :=
point.mk (n * p.x) (n * p.y)

def p : point ℕ := point.mk 1 2

#reduce p.smul 3  -- {x := 3, y := 6}

#check { point . x := 10, y := 20 }  -- point ℕ
#check { point . y := 20, x := 10 }
#check ({x := 10, y := 20} : point _)

example : point _ := { y := 20, x := 10 }

structure my_struct :=
mk :: {α : Type} {β : Type} (a : α) (b : β)

#check { my_struct . a := 10, b := true }

#reduce {y := 3, ..p}  -- {x := 1, y := 3}
#reduce {x := 4, ..p}  -- {x := 4, y := 2}

structure point3 (α : Type) :=
mk :: (x : α) (y : α) (z : α)

def q : point3 nat :=
{x := 5, y := 5, z := 5}

def r : point3 nat := {x := 6, ..p, ..q}

#print r  -- {x := 6, y := p.y, z := q.z}
#reduce r  -- {x := 6, y := 2, z := 5}

inductive color
| red | green | blue

structure color_point (α : Type) extends point α :=
mk :: (c : color)

#print color_point
#print prefix color_point

structure rgb_val :=
(red : nat) (green : nat) (blue : nat)

structure red_green_point (α : Type) extends point3 α, rgb_val :=
(no_blue : blue = 0)

def p'   : point3 nat := {x := 10, y := 10, z := 20}
def rgp : red_green_point nat :=
{red := 200, green := 40, blue := 0, no_blue := rfl, ..p'}

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl

#print red_green_point