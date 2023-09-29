theory Queue
imports Main
begin

datatype 'a List = N | C 'a "'a List"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
    "app N ys = ys"
  | "app (C x xs) ys = C x (app xs ys)"

fun reverse :: "'a List \<Rightarrow> 'a List" where
    "reverse N = N"
  | "reverse (C x xs) = app (reverse xs) (C x N)"


export_code reverse in Haskell file "out/"
export_code reverse in Haskell module_name "Queue"

lemma app_nil[simp]: "app xs N = xs"
  apply (induction xs)
   apply auto
  done

lemma app_assoc: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
   apply auto
  done

lemma reverse_app: "reverse (app xs ys) = app (reverse ys) (reverse xs)"
  apply (induction xs)
   apply (auto simp add: app_assoc)
  done

lemma reverse_reverse[simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto simp add: reverse_app)
  done

fun len :: "'a List => nat" where
    "len N = 0"
  | "len (C x xs) = 1 + (len xs)"

lemma nil_length: "len xs = 0 \<Longrightarrow> xs = N"
  apply (induction xs)
   apply auto
  done

lemma app_length[simp]: "len (app xs ys) = (len xs) + (len ys)"
  apply (induction xs)
   apply auto
  done

lemma reverse_length: "len (reverse xs) = len xs"
  apply (induction xs)
   apply auto
  done

lemma reverse_equal: "len xs \<le> 1 \<Longrightarrow> reverse xs = xs"
  apply (induction xs)
  apply (auto dest: nil_length)
  done  

fun idx :: "'a List \<Rightarrow> nat \<Rightarrow> 'a option" where
    "idx N n = None"
  | "idx (C x xs) 0 = Some x"
  | "idx (C x xs) n = idx xs (n-1)"

lemma idx_length[simp]: "idx xs (len xs) = None"
  apply (induction xs)
   apply auto
  done

lemma sucE: "n < Suc m \<Longrightarrow> n < m \<or> n = m"
  by auto

fun first :: "'a List \<Rightarrow> 'a option" where
    "first N = None"
  | "first (C x xs) = Some x"

fun lastt :: "'a List \<Rightarrow> 'a option" where
    "lastt N = None"
  | "lastt (C x xs) = first (reverse (C x xs))"

lemma idx_app_0[simp]: "idx (app (C x N) xs) 0 = Some x"
  by auto

lemma idx_C_n: "0 < (n::nat) \<Longrightarrow> idx (C x xs) n = idx xs (n-1)"
  apply (induction xs)
   apply auto
  apply (metis List.inject bot_nat_0.not_eq_extremum idx.elims idx.simps(1))
  by (metis One_nat_def gr0_implies_Suc idx.simps(3))

lemma idx_app_n: "0 < n \<Longrightarrow> idx (app (C x N) xs) n = idx xs (n-1)"
  apply (induction xs)
  by (simp_all add: idx_C_n)


lemma app_C_N: "app (C x N) xs = C x xs"
  by auto

lemma app_C: "C x (app xs ys) = app (C x xs) ys"
  by auto

lemma b0: "n < len as \<Longrightarrow> idx (app as bs) n = idx as n"
  apply (induction as)
   apply auto
  



lemma b1: "n < len xs \<Longrightarrow> idx (reverse xs) n = idx xs ((len xs) - n - 1)"
  apply (induction n)
   apply auto
   apply (induction xs)
    apply auto



lemma bla: "n = len xs \<Longrightarrow> idx (app (reverse xs) (C x N)) (len xs - n) = lastt xs"

lemma reverse_def: "n < len xs \<Longrightarrow> idx (reverse xs) (len xs - n - 1)  = idx xs n"
  apply (induction n)
  apply auto
  
  apply (induction xs)
   apply auto
  apply (auto dest: sucE)
  apply (induction n)
  apply auto

fun butfirst :: "'a List \<Rightarrow> 'a List" where
    "butfirst N = N"
  | "butfirst (C x xs) = xs"

fun butlastt :: "'a List \<Rightarrow> 'a List" where
    "butlastt N = N"
  | "butlastt (C x xs) = reverse (butfirst (reverse (C x xs)))"

function palin :: "'a List \<Rightarrow> bool" where
    "palin N = True"
  | "palin (C x xs) = ((Some x = lastt xs) \<and> palin (butlastt xs))"
     apply simp_all
  apply (auto dest: impI)
     apply auto

lemma palin_reverse_equal: "palin xs \<Longrightarrow> reverse xs = xs"


lemma reverse_not_equal: "1 < len xs \<Longrightarrow> reverse xs \<noteq> xs"
  apply (induction xs)
  apply auto
  sorry

end
