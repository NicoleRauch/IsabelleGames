theory ToyList2
imports Main
begin

hide_type (open) list
hide_const (open) last length append

datatype 'a List = N | C 'a "'a List"

fun append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "append N ys = ys" |
  "append (C x xs) ys = C x (append xs ys)"

fun reverse :: "'a List \<Rightarrow> 'a List" where
  "reverse N = N" |
  "reverse (C x xs) = append (reverse xs) (C x N)"

lemma append_nil [simp]: "append xs N = xs"
  by (induction xs, auto)

lemma append_assoc [simp]: "append (append xs ys) zs = append xs (append ys zs)"
  by (induction xs, auto)

lemma reverse_append [simp]: "reverse (append xs ys) = append (reverse ys) (reverse xs)"
  by (induction xs, auto)

lemma reverse_reverse [simp]: "reverse (reverse xs) = xs"
  by (induction xs, auto)

theorem reverse_pred:
  fixes f :: "'a List \<Rightarrow> 'a List"
  assumes
    "f N = N" and
    "\<And>x. f (C x N) = C x N" and
    "\<And>xs ys. f (append xs ys) = append (f ys) (f xs)"
  shows "f = reverse"
proof -
  { fix xs :: "'a List"
    from assms have "f xs = reverse xs"
    proof (induction xs)
      case N thus ?case by simp
      case (C x ys) thus ?case
      proof auto
        from C.prems(2) have "f (C x N) = C x N" by simp
        moreover
        have "C x ys = append (C x N) ys" by auto
        with C.prems(3) have "f (C x ys) = append (f ys) (f (C x N))" by metis
        moreover
        assume "f ys = reverse ys"
        ultimately
        show "f (C x ys) = append (reverse ys) (C x N)" by simp
      qed
    qed
  } thus ?thesis by (rule ext)
qed

end
