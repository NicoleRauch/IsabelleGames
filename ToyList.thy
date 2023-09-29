theory ToyList
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


abbreviation length :: "'a List \<Rightarrow> nat" where
  "length \<equiv> size"

fun idx :: "'a List \<Rightarrow> nat \<Rightarrow> 'a option" where
  "idx N _ = None" |
  "idx (C x xs) 0 = Some x" |
  "idx (C x xs) (Suc n) = idx xs n"

fun first :: "'a List \<Rightarrow> 'a option" where
  "first N = None" |
  "first (C x xs) = Some x"

fun last :: "'a List \<Rightarrow> 'a option" where
  "last N = None" |
  "last (C x N) = Some x" |
  "last (C x xs) = last xs"

abbreviation idx_rev :: "'a List \<Rightarrow> nat \<Rightarrow> 'a option" where
  "idx_rev xs n \<equiv> (if n < length xs then idx xs (length xs - (Suc n)) else None)"


lemma list_induct2:
  "P N N \<Longrightarrow>
  (\<And>x xs. P (C x xs) N) \<Longrightarrow>
  (\<And>y ys. P N (C y ys)) \<Longrightarrow>
  (\<And>x xs y ys. P xs ys \<Longrightarrow> P (C x xs) (C y ys))
 \<Longrightarrow> P xs ys"
  by (induct xs arbitrary: ys) (case_tac x, auto)+

lemma zero_length_nil: "length xs = 0 \<equiv> xs = N"
  by (induction xs, auto)

lemma append_length [simp]: "length (append xs ys) = length xs + length ys"
  by (induction xs ys rule: append.induct, auto)

lemma length_reverse[simp]: "length (reverse xs) = length xs"
  by (induction xs, auto)

lemma first_idx: "first xs = idx xs 0"
  by (induction xs, auto)

lemma last_idx: "last xs = idx xs (length xs - 1)"
proof (induction xs, simp)
  case (C x xs) thus ?case by (cases xs, auto)
qed

lemma idx_append1: "n < length xs \<Longrightarrow> idx (append xs ys) n = idx xs n"
proof (induction xs arbitrary: n)
  case N thus ?case by simp
next
  case (C x xs) thus ?case by (induction n, auto)
qed

lemma idx_append2: "n \<ge> length xs \<Longrightarrow> idx (append xs ys) n = idx ys (n - length xs)"
proof (induction xs arbitrary: n)
  case N thus ?case by simp
next
  case (C x xs) thus ?case by (induction n, auto)
qed

lemma idx_eq_none: "idx xs n = None \<Longrightarrow> n \<ge> length xs"
  by (induction xs n rule: idx.induct, auto)

lemma idx_eq_some: "idx xs n = Some x \<Longrightarrow> n < length xs"
  by (induction xs n rule: idx.induct, auto)

lemma idx_out_of_bounds: "n \<ge> length xs \<Longrightarrow> idx xs n = None"
  by (induction xs n rule: idx.induct, auto)

lemma idx_within_bounds:
  "n < length xs \<Longrightarrow> \<exists>x. idx xs n = Some x"
  "n < length xs \<Longrightarrow> idx xs n \<noteq> None"
  by (induction xs n rule: idx.induct, auto)

lemma idx_rev_out_of_bounds: "n \<ge> length xs \<Longrightarrow> idx_rev xs n = None"
  by (induction xs n rule: idx.induct, auto)

lemma idx_rev_within_bounds:
  "n < length xs \<Longrightarrow> \<exists>x. idx_rev xs n = Some x"
  "n < length xs \<Longrightarrow> idx_rev xs n \<noteq> None"
  by (auto simp: idx_within_bounds)

lemma last_append: "ys = N \<or> last (append xs ys) = last ys"
proof (induction xs, simp)
  case (C x xs) thus ?case
    by (metis last.simps(3) append.elims append.simps(2))
qed

lemma last_append2: "ys \<noteq> N \<Longrightarrow> last (append xs ys) = last ys"
  using last_append by fast

lemmas last_append_cons = last_append2[OF List.distinct(2)]

lemma first_eq_last_reverse: "first xs = last (reverse xs)"
proof (induction xs, simp)
  case (C x xs) thus ?case
  proof -
    { fix x :: 'a and xs :: "'a List"
      have "last (append xs (C x N)) = Some x"
      proof (induction xs)
        case N show ?case by simp
      next
        case (C a as)
        with last_append_cons[of "C a as" x N]
        show ?case by simp
      qed
    } with C show ?case by simp
  qed
qed


theorem idx_reverse: "idx xs n = idx_rev (reverse xs) n"
proof -
  have "n < length xs \<Longrightarrow> idx xs n = idx_rev (reverse xs) n"
  proof (induction xs arbitrary: n)
    case N thus ?case by simp
  next
    case (C x xs)
    obtain rhs rhs' rhs'' where
      rhs_def : "rhs = idx_rev (reverse (C x xs)) n" and
      rhs'_def: "rhs' = idx (append (reverse xs) (C x N)) (length xs - n)" and
      rhs''_def: "rhs'' = idx (reverse xs) (length xs - n)"
      by simp
    from C.prems have "rhs = rhs'"
      unfolding rhs_def rhs'_def
      by simp

    show ?case
    proof (cases "n = length xs")
      case True
      hence len_minus_n: "0 = length xs - n" and
            nEq:         "n = length (C x xs) - 1"
        by auto
      from first_idx[of "reverse (C x xs)", symmetric]
      have "rhs' = first (reverse (C x xs))"
        unfolding rhs'_def reverse.simps(2)
        by (rule_tac subst[OF len_minus_n], clarify)
      note
        (* idx (C x xs) n = last (C x xs) *)
        ssubst[OF nEq,
               of "\<lambda>n. last (C x xs) = idx (C x xs) n",
               OF last_idx,
               symmetric]
        (* last (C x xs) = rhs *)
        subst[OF reverse_reverse[of "C x xs"],
              of "\<lambda>l. rhs = last l",
              OF trans[OF `rhs = rhs'` trans[OF this first_eq_last_reverse]],
              symmetric]
      from trans[OF this] show ?thesis unfolding rhs_def .
    next
      case False
      with `n < length (C x xs)` have "length xs > 0" by auto

      show ?thesis
      proof (cases n)
        case 0 hence "length xs \<le> length xs - n" and
                     "length xs - n - length xs = 0"
          by auto
        from idx_append2[OF this(1), of "C x N"] this(2) `n = 0`
             idx_append2[of "reverse xs"]
        have "rhs = idx (C x N) 0" unfolding rhs_def by auto
        with `n = 0` show ?thesis unfolding rhs_def
          by clarsimp
      next
        have cons_app: "C x xs = append (C x N) xs" by simp
        case (Suc m) hence "length (C x N) \<le> n" and "n \<noteq> 0" by auto
        from ssubst[OF cons_app,
                    of "\<lambda>as. idx as n = idx xs (n - length (C x N))",
                    OF idx_append2[OF this(1), of xs]]
        have "idx (C x xs) n = idx xs (n - 1)" by simp
        also
        {
          from C(2) Suc have "n - 1 < length xs" by simp
          note C.IH[OF this]
          moreover
          from `n \<noteq> 0` have "Suc (n - 1) = n" by arith
          ultimately
          have "idx xs (n - 1) = rhs''"
            using `n - 1 < length xs`
            unfolding rhs''_def
            by force
        }
        also
        from `n \<noteq> 0` `length xs > 0`
        have "(length (reverse xs) - n) < length (reverse xs)"
          by fastforce
        from idx_append1[OF this]
        have "rhs' = rhs''" unfolding rhs'_def rhs''_def by simp
        note trans[OF `rhs = rhs'` this, symmetric]
        finally show ?thesis unfolding rhs_def .
      qed
    qed
  qed
  thus ?thesis
    by (simp add: idx_out_of_bounds)
qed


(* Beweis:
   idx_reverse ist hinreichend, um reverse (eindeutig) zu charakterisieren.
*)

lemma list_eq_idx: "(\<forall>n. idx xs n = idx ys n) \<Longrightarrow> xs = ys"
proof (induction xs ys rule: list_induct2)
  case 1 thus ?case by simp
next
  case (2 x xs) thus ?case
    by (metis idx.simps(1) first.simps(2) first_idx option.distinct(1))
next
  case (3 y ys) thus ?case
    by (metis idx.simps(1) first.simps(2) first_idx option.distinct(1))
next
  case (4 x xs y ys) thus ?case
    by (metis idx.simps(3) first.simps(2) first_idx option.inject)
qed

lemma idx_rel_impl_len_eq:
  fixes f :: "'a List \<Rightarrow> 'a List" and xs :: "'a List"
  assumes "\<And>xs n. idx xs n = idx_rev (f xs) n"
  shows "length xs = length (f xs)"
proof (rule ccontr)
  assume len_neq: "length xs \<noteq> length (f xs)"
  thus False
  proof (cases "length xs < length (f xs)")
    case True
    obtain n where n_def: "n = length xs" by simp
    note (* idx_rev (f xs) n = None *)
      ssubst[OF this,
             of "\<lambda>k. idx_rev (f xs) k = None",
             OF trans[OF assms[symmetric]
                         idx_out_of_bounds[of xs "length xs", simplified]]]
    moreover
    from True n_def have "n < length (f xs)" by simp
    note (* idx_rev (f xs) n \<noteq> None *)
      idx_rev_within_bounds(2)[OF this]
    ultimately show False by clarsimp
  next
    case False with len_neq
    have len_lem: "length (f xs) < length xs" by simp
    obtain n where n_def: "n = length (f xs)" by simp
    hence "idx_rev (f xs) n = None" by simp
    note (* idx xs n = None *)
      trans[OF assms this]
    moreover
    from len_lem n_def have "n < length xs" by simp
    note (* idx xs n \<noteq> None *)
      idx_within_bounds(2)[OF this]
    ultimately show False by clarsimp
  qed
qed


theorem reverse_pred:
  fixes f :: "'a List \<Rightarrow> 'a List"
  assumes "\<And>x xs n. idx xs n = idx_rev (f xs) n"
  shows "f = reverse"
proof -
  note len_f = idx_rel_impl_len_eq[OF assms]
  { fix xs :: "'a List"
    from assms have "f xs = reverse xs"
    proof (induction xs rule: reverse.induct)
      case 1 thus ?case
      proof auto
        from len_f have "length (f N) = 0" by simp
        thus "f N = N" using zero_length_nil by blast
      qed
    next
      case (2 x xs) thus ?case
      proof (intro list_eq_idx, intro strip)
        fix n show "idx (f (C x xs)) n = idx (reverse (C x xs)) n"
        proof (cases "idx (f (C x xs)) n")
          case None
          from idx_eq_none[OF this] len_f[of "C x xs"]
          have "length (reverse (C x xs)) \<le> n" by clarsimp
          from idx_out_of_bounds[OF this] None
          show ?thesis by simp
        next
          case (Some a)
          from idx_eq_some[OF this] len_f
          have "n < length (C x xs)" by simp
          hence "n \<le> length xs" by simp
          then obtain k where "k = length xs - n" by simp
          with `n \<le> length xs`
          have k_lt_len  : "k < length (C x xs)" and
               n_eq_len_k: "n = length (C x xs) - Suc k"
            by simp_all
          with idx_reverse[of "C x xs" k]
          have "idx (C x xs) k = idx (reverse (C x xs)) n"
            by simp
          also
          from 2(2)[of "C x xs" k] k_lt_len n_eq_len_k len_f
          have "idx (C x xs) k = idx (f (C x xs)) n"
            by simp
          finally show ?thesis .
        qed
      qed
    qed
  } thus ?thesis by (rule ext)
qed

end
