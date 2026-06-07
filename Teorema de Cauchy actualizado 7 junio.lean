import Mathlib.Tactic

--Sea G un grupo finito
variable (G : Type) [Group G] [Fintype G]
--Sea p un entero primo
variable (p : ℤ) (hp : Prime p)

--Definimos el teorema de Cauchy
--Sea G un cuerpo fnito y p un primo tal que p | |G|, entonces, G tiene un elemento de orden p

--Esta es la proposicion clave que usa el teorema para demostrar que el cardinal de las orbitas de C sobre S divide a p
theorem proposition2_1 (G S : Type) [Group G] [Fintype G] [MulAction G S] (s:S):  
     (MulAction.stabilizer G s).index = Nat.card (MulAction.orbit G s) := by sorry

theorem card_orbita (G S : Type) (n : ℕ) [Group G] [Fintype G] [MulAction G S] (h_prim : Nat.Prime n) (h_zero : n≠ 0) (h_card : Nat.card G = n) (s:S) : Nat.card (MulAction.orbit G s) ∣ n := by
    have h1 : (MulAction.stabilizer G s).index = Nat.card (MulAction.orbit G s) := by exact proposition2_1 G S s
    have h2 : (MulAction.stabilizer G s).index * Nat.card (MulAction.stabilizer G s) = Nat.card G := by exact Subgroup.index_mul_card (MulAction.stabilizer G s)
    have h3 : (MulAction.stabilizer G s).index * Nat.card (MulAction.stabilizer G s) = n := by rw[h2 ,h_card]
    have h4 : (MulAction.stabilizer G s).index ∣ n := by exact Dvd.intro (Nat.card ↥(MulAction.stabilizer G s)) h3
    rw[h1] at h4
    exact h4

--Definimos un resultado para mostrar que si tenemos a,b b primo tal que a|b, entonces a = 1 o a = b

theorem primo_divisor (a b : ℕ) (h_es_primo : Nat.Prime b) (h_divide : a ∣ b) : a = 1 ∨ a = b := by exact (Nat.dvd_prime h_es_primo).mp h_divide

--Definimos este resultado para usarlo en la parte de reduccion al absurdo
theorem si_no_uno_otro (a b : ℕ ) (h_uno_otro : a = 1 ∨ a = b ) (h_no_uno : a ≠ 1) : a = b := by exact Or.resolve_left h_uno_otro h_no_uno

theorem division_orbita (G S : Type) (n : ℕ) [Group G] [Fintype G] [Fintype S] [MulAction G S] (h_prim : Nat.Prime n) (h_zero : n≠ 0) (h_card : Nat.card G = n) (h_todo_igual : ∀ (s:S), (Nat.card (MulAction.orbit G s)) = n) : ∀ (s:S), (Nat.card (MulAction.orbit G s)) ∣ Nat.card S := by sorry


--Defino aqui un resultado que me va a ayudar a simpplificar la parte del cardinal del conjunto |S|
--Lo que queremos mostrar a Lean con este teorema es que hay una biyeccion entre una coleccion de (n-1) elementos de G y T, lo cual viene a decir que cualquier elemento de T esta formado por (n-1) elementos de G, y es evidente de ver en papel pero en Lean es más complicado

def equiv_T (G : Type) [Group G] [Fintype G] (n : ℕ) : (Fin (n - 1) → G) ≃ { t : (Fin n → G) // (List.ofFn t).prod = 1 } := by sorry

--Definimos aqui otro resultado para simplificar la demostracion de que |S|=|T|-1, simplemente definimos una equivalencia que dice que el cardinal de T equivale a S más otro elemento

def equiv_S (G : Type) [Group G] [Fintype G] (n : ℕ) : { t : (Fin n → G) // (List.ofFn t).prod = 1 } ≃ Option { s : (Fin n → G) // (List.ofFn s).prod = 1 ∧ s ≠ (fun _ => 1)} := by sorry

def div_potencia (a b pow : ℕ) (h_div_b : a ∣ b) (h_pow : pow ≠ 0):  a ∣ b^pow := by exact Dvd.dvd.pow h_div_b h_pow

def no_div_potencia_1 (a b : ℕ  ) (h_a : a > 1) (h_b : b>0) (h_div_ab :  a ∣ b) : ¬ (a ∣ b-1) := by
   sorry

theorem cauchy_theorem (p : ℤ) (G : Type) [Group G] [Fintype G] (hp : Prime p) (h_no_one : p ≠ 0) (h_div : p.natAbs ∣ Fintype.card G) : 
  ∃ g : G, orderOf g = p.natAbs := by
   --Paso 1: Construimos el producto de G y tomamos S < G
   -- 1. Definimos n como el natural p.natAbs para simplificar tenemos que mostrar que el valor absoluto de p primo es un natural primo
  let n := p.natAbs
  letI : Nat.Prime n := Int.prime_iff_natAbs_prime.mp hp
  have n_prime : Nat.Prime n := Int.prime_iff_natAbs_prime.mp hp --Defino la hipotesis para poder usarla luego en los teoremas
  have n_no_zero : n ≠ 0 := by exact Int.natAbs_ne_zero.mpr h_no_one
  haveI : NeZero n := ⟨n_no_zero⟩ --Hay que explicar bien para que sirve esto
  haveI : n ≠ 0 := by exact Int.natAbs_ne_zero.mpr h_no_one

  -- 2. Definimos el tipo de las secuencias G^n
  let Vec := Fin n → G
  --letI : Group Vec := Pi.group Aquí lo que indicamos, es que un producto de grupos es un grupo
  letI : Fintype Vec := Pi.instFintype --Aqui lo que indicamos es que un grupo de fintypes es fintype
  -- 3. Definimos S 
  let vector_unitario : Vec := fun _ => 1  --Definimos el vector (1,1,1,.....,1)

  let S := { s : Vec // (List.ofFn s).prod = 1 ∧ s ≠ vector_unitario}

  haveI : Fintype S := by exact Fintype.ofFinite S --Tenemos que mostrar que S y T son finitos para poder usar la funcion cardinal

  let T := { t : Vec // (List.ofFn t).prod = 1} --Definimos el conjunto T para mostrar que su cardinal es |G|^(n-1)
  have : Fintype T := by exact Fintype.ofFinite T

  --Paso 2: Tomamos un s en S y mostramos que p no divide a |S|
  -- Hay que mostrar que |S| = |G|^p-1 - 1  
  haveI h_card_T : Fintype.card T = (Fintype.card G)^(n - 1) := by
    --Tenemos que mostrar que un e en T tiene (n-1) elementos libres, aqui podemos usar el resultado equiv_T
    calc Fintype.card T
      _ = Fintype.card (Fin (n - 1) → G) := Fintype.card_congr (equiv_T G n).symm
      _ = (Fintype.card G) ^ (n - 1) := by simp
  haveI h_card_s : Fintype.card S = (Fintype.card G)^(n - 1) -1  := by
    have h_S_mas : Fintype.card T = Fintype.card S + 1 := by
      calc Fintype.card T
      _ = Fintype.card (Option S) := Fintype.card_congr (equiv_S G n)
      _ = Fintype.card S + 1 := Fintype.card_option
    omega --omega nos resuelve la linealidad
  have h_para_contradiccion : ¬ n ∣ Fintype.card S := by
    have h_n_no_one : n ≠ 1 := by (expose_names; exact Nat.Prime.ne_one this_1)
    have h_n_no_zero : n-1 ≠ 0 := by omega
    have h_pw : n ∣ (Fintype.card G)^(n-1) := by exact div_potencia n (Fintype.card G) (n-1) h_div h_n_no_zero
    have h_sup_uno : n > 1 := by (expose_names; exact Nat.Prime.one_lt this_1)
    have h_sup_zero : (Fintype.card G)^(n-1) > 0 := by exact Nat.pos_of_neZero (Fintype.card G ^ (n - 1))
    have h_no_div_n : ¬ n ∣ ((Fintype.card G)^(n-1) -1) := by exact no_div_potencia_1 n ((Fintype.card G)^(n-1)) h_sup_uno h_sup_zero h_pw
    exact Eq.mpr_not (congrArg (Dvd.dvd n) h_card_s) h_no_div_n --Esto me lo ha resuelto el "exact?"
  
  --Paso 3: Definimos el grupo ciclico C = <z>
  
  
  let C := Multiplicative (ZMod n) 
  letI h_grupo : Group C := Multiplicative.group
  haveI h_finito : Fintype C := by 
     infer_instance
  have cardinal_c : Nat.card C = n := by
    simp only [Nat.card_eq_fintype_card]
    have h : Fintype.card (ZMod n) = n := by exact ZMod.card n
    have h2 : (Fintype.card C) = Fintype.card (ZMod n) := by exact Fintype.card_congr' rfl
    rw[h] at h2
    exact h2

  haveI hC_ciclico : IsCyclic C := by infer_instance

  let c_fin (c : C) : Fin n := ⟨(Multiplicative.toAdd c).val, ZMod.val_lt (Multiplicative.toAdd c)⟩ --Esto transforma un elemento de c en un indice para sumarselo al vector

  letI h_accion : MulAction C S := {
    --Una vez definida la accion tenemos que mostrar que:
    --  1)La multiplicacion de los elementos del vector nuevo sigue siendo 1
    --  2)No es el vector unitario
    smul := fun c s => ⟨fun i => s.val (i + c_fin c), by
      have ⟨vector, propiedad_1, propiedad_2⟩ := s --Aqui obtenemos el vector en si y sus dos propiedades (que la multiplicacion de sus elementos es 1 y que es diferente del unitario)
      dsimp only --Esto simplifica lo que tenemos que demostrar en el compilador, ahora el objetivo es claro y es el que hemos enunciado
      constructor --Aqui dividimos los dos objetivos que queremos demostrar
      have h_listas : List.ofFn (fun i => vector (i + c_fin c)) = (List.ofFn vector).rotate (c_fin c).val := by
        apply List.ext_get
        simp
        intro i h1 h2
        simp only [List.get_ofFn, List.get_rotate]
        congr 1
        ext
        simp
        exact Fin.coe_ofNat_eq_mod n (i + (Multiplicative.toAdd c).val)
         --Esto lo necesito para poder usar la funcion "List.prod_rotate_eq_one_of_prod_eq_one propiedad_1 ↑(c_fin c)""
      rw[h_listas]
      exact List.prod_rotate_eq_one_of_prod_eq_one propiedad_1 ↑(c_fin c)
      intro h_absurdo
      apply propiedad_2
      ext i --Cogemos un elemento cualquiera del vector
      have h_eval := congr_fun h_absurdo (i - c_fin c)
      have h: vector i = vector (i - c_fin c + c_fin c)  := by
        have h1 : i = i - c_fin c + c_fin c := by simp
        rw[← h1]
      rw[← h] at h_eval
      exact (MulOpposite.op_eq_one_iff (vector i)).mp (congrArg MulOpposite.op h_eval)

      ⟩ 

    --Aqui tenemos que mostrar que la accion del elemento neutro no altera el vector
    one_smul := by
      intro s
      ext i
      change s.val (i + c_fin 1) = s.val i
      have h_neutro : c_fin 1 = 0 := by
        apply Fin.ext
        change ZMod.val 0 = 0
        exact ZMod.val_zero
      rw[h_neutro]
      simp
    
    --Aqui tenemos que mostrar la asociatividad de la accion
    mul_smul := by
      intro a b s
      ext i
      change s.val (i + c_fin (a*b))= s.val (i + c_fin a + c_fin b)
      have h :  c_fin (a*b) = c_fin a + c_fin b := by
        apply Fin.ext
        change (Multiplicative.toAdd (a*b)).val = ((Multiplicative.toAdd a).val +(Multiplicative.toAdd b).val)%n
        exact ZMod.val_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)
      rw[h]
      have h1 : i + (c_fin a + c_fin b) = i + c_fin a + c_fin b := by exact Eq.symm (add_assoc i (c_fin a) (c_fin b))
      rw[h1]
  }




  --Paso 4: Usamos la proposicion 2.1 para mostrar que |Orb_C(s)| | p

  let estabilizador (s : S) := MulAction.stabilizer C s


  have hOfinito : ∀ s:S, Fintype (MulAction.orbit C s) := by exact fun s => Fintype.ofFinite ↑(MulAction.orbit C s)
  --Con hOfinito Lean ya sabe que la orbita Cs es finita
  

  have hipotesis_p_div (s:S): Nat.card (MulAction.orbit C s) ∣  n := by exact card_orbita C S n n_prime n_no_zero cardinal_c s
  
  have hipotesis_p_div_general : ∀ (s:S), Nat.card (MulAction.orbit C s) ∣  n := by (expose_names; exact fun s => card_orbita C S n this_1 n_no_zero cardinal_c s)

  --Paso 5: Mostramos que existe Orb_C(s) tal que |Orb_C(s)| = 1

  have h_p_o_1 (s:S) : Nat.card (MulAction.orbit C s) = 1 ∨ Nat.card (MulAction.orbit C s) = n := by
    exact primo_divisor (Nat.card (MulAction.orbit C s)) n n_prime (hipotesis_p_div s)

  --Generalizamos para todo s  
  have h_p_o_1_general : ∀ (s:S), Nat.card (MulAction.orbit C s) = 1 ∨ Nat.card (MulAction.orbit C s) = n := by (expose_names; exact fun s => primo_divisor (Nat.card ↑(MulAction.orbit C s)) n this_1 (hipotesis_p_div s))

  --Aqui hay que desarrollar un razonamiento por absurdo
  have h_existe_card_1 : ∃ s:S, Nat.card (MulAction.orbit C s) = 1 := by
    by_contra! h_absurdo
    have h_n : ∀ (s : S), Nat.card (MulAction.orbit C s) = n := by
      exact fun s => si_no_uno_otro (Nat.card ↑(MulAction.orbit C s)) n (h_p_o_1 s) (h_absurdo s)
    have h_falso : n ∣ Fintype.card S := by
      have h_o_d : ∀ (s : S), Nat.card (MulAction.orbit C s) ∣ Nat.card S := by (expose_names; exact fun s => division_orbita C S n this_1 n_no_zero cardinal_c h_n s)
      rw [Fintype.card_eq_nat_card]
      by_cases vacio : Nonempty S
      --Caso S no vacio
      let s := Classical.arbitrary S
      have h1 : Nat.card (MulAction.orbit C s) = n := by exact si_no_uno_otro (Nat.card ↑(MulAction.orbit C s)) n (h_p_o_1 s) (h_absurdo s)
      have h2 : Nat.card (MulAction.orbit C s) ∣ Nat.card S := by (expose_names; exact division_orbita C S n this_1 n_no_zero cardinal_c h_n s)
      rw[h1] at h2
      exact h2
      --Caso S vacio
      haveI : IsEmpty S := by exact not_nonempty_iff.mp vacio
      have h_card : Nat.card S = 0 := by exact Nat.card_of_isEmpty
      rw[h_card]
      exact Nat.dvd_zero n
    exact h_para_contradiccion h_falso
  
  have s_clave : (∃ s:S, Nat.card (MulAction.orbit C s) = 1) → (∃ s:S , ∀ c:C, (fun i => s.val (i + c_fin c)) = s.val) := by
    intro h_existe
    rcases h_existe with ⟨s, h_card_1⟩
    use s
    intro c

    have h_card_fin : Fintype.card (MulAction.orbit C s) = 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact h_card_1
    have ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp h_card_fin --Con esto tenemos que la orbita tiene exactamente un elemento x y la prueba de que todos los y de la orbita son x

    have h_mem_cs : SMul.smul c s ∈ MulAction.orbit C s := ⟨c, rfl⟩
    have h_mem_s : s ∈ MulAction.orbit C s := MulAction.mem_orbit_self s

    let cs_orb : MulAction.orbit C s := ⟨SMul.smul c s, h_mem_cs⟩
    let s_orb : MulAction.orbit C s := ⟨s, h_mem_s⟩
    
    have igual : cs_orb = s_orb := (hx cs_orb).trans (hx s_orb).symm --Por transitividad y simetría, los dos son iguales a x por hx, entonces son iguales entre si
    have h_eq : SMul.smul c s = s := congrArg Subtype.val igual

    exact congrArg Subtype.val h_eq

  have existe_s : ∃ s:S , ∀ c:C, (fun i => s.val (i + c_fin c)) = s.val := by exact Exists.imp (fun a a_1 => a_1) (s_clave h_existe_card_1)

  rcases existe_s with ⟨s_final, h_invariante⟩

  have h_todos_iguales : ∀ i, s_final.val i = s_final.val 0 := by
    by_contra! h_absurdo
    rcases h_absurdo with ⟨i_malo, h_distinto⟩
    let c : C := Multiplicative.ofAdd (i_malo.val : ZMod n)
    have h_no_igual : (fun i => s_final.val (i + c_fin c)) ≠ s_final.val := by
      intro h_falsa_igualdad
      have h_eval := congr_fun h_falsa_igualdad 0
      have h_idx : 0 + c_fin c = i_malo := by
        apply Fin.ext
        rw [zero_add]
        change ((i_malo.val : ZMod n)).val = i_malo.val
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt i_malo.isLt
      rw[h_idx] at h_eval
      exact h_distinto h_eval
    exact h_no_igual (h_invariante c)
        




  --Paso 6 Final: Mostramos que como ∃ s:S tal que |Orb_C(s)| = 1, entonces existe x ∈ G tal que x^p = 1
  have hfinal: ∃ g:G, orderOf g = p.natAbs := by
    have s_g : ∃ g:G, ∀ i, s_final.val i = g := by
      sorry
    rcases s_final with ⟨valor, propiedad_1,propiedad_2⟩
    sorry
     
    

  exact hfinal