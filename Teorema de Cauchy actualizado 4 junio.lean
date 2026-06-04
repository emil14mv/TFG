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
  have h1 : ¬ n ∣ Fintype.card S := by
    have h_n_no_one : n ≠ 1 := by (expose_names; exact Nat.Prime.ne_one this_1)
    have h_n_no_zero : n-1 ≠ 0 := by omega
    have h_pw : n ∣ (Fintype.card G)^(n-1) := by exact div_potencia n (Fintype.card G) (n-1) h_div h_n_no_zero
    have h_sup_uno : n > 1 := by (expose_names; exact Nat.Prime.one_lt this_1)
    have h_sup_zero : (Fintype.card G)^(n-1) > 0 := by exact Nat.pos_of_neZero (Fintype.card G ^ (n - 1))
    have h_no_div_n : ¬ n ∣ ((Fintype.card G)^(n-1) -1) := by exact no_div_potencia_1 n ((Fintype.card G)^(n-1)) h_sup_uno h_sup_zero h_pw
    exact Eq.mpr_not (congrArg (Dvd.dvd n) h_card_s) h_no_div_n --Esto me lo ha resuelto el "exact?"
  
  --Paso 3: Definimos el grupo ciclico C = <z>
  
  
  let C := Multiplicative (ZMod n) 
  haveI h_grupo : Group C := Multiplicative.group
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

  haveI h_accion : MulAction C S := {
    --Una vez definida la accion tenemos que mostrar que:
    --  1)La multiplicacion de los elementos del vector nuevo sigue siendo 1
    --  2)No es el vector unitario
    smul := fun c s => ⟨fun i => s.val (i + c_fin c), by
      have ⟨vector, propiedad_1, propiedad_2⟩ := s --Aqui obtenemos el vector en si y sus dos propiedades (que la multiplicacion de sus elementos es 1 y que es diferente del unitario)
      dsimp only --Esto simplifica lo que tenemos que demostrar en el compilador, ahora el objetivo es claro y es el que hemos enunciado
      constructor --Aqui dividimos los dos objetivos que queremos demostrar
      have h_listas : List.ofFn (fun i => vector (i + c_fin c)) = (List.ofFn vector).rotate (c_fin c).val := by
        sorry --Esto lo necesito para poder usar la funcion "List.prod_rotate_eq_one_of_prod_eq_one propiedad_1 ↑(c_fin c)""
      rw[h_listas]
      exact List.prod_rotate_eq_one_of_prod_eq_one propiedad_1 ↑(c_fin c)
      intro h_absurdo
      apply propiedad_2
      ext i --Cogemos un elemento cualquiera del vector
      have h_eval := congr_fun h_absurdo (i - c_fin c)
      have h: vector i = vector (i - c_fin c + c_fin c)  := by sorry
      rw[← h] at h_eval
      exact (MulOpposite.op_eq_one_iff (vector i)).mp (congrArg MulOpposite.op h_eval)

      ⟩ 

    --Aqui tenemos que mostrar que la accion del elemento neutro no altera el vector
    one_smul := by 
      sorry
    
    --Aqui tenemos que mostrar la asociatividad de la accion
    mul_smul := by 
      sorry
  }




  --Paso 4: Usamos la proposicion 2.1 para mostrar que |Orb_C(s)| | p


  have hOfinito : ∀ s:S, Fintype (MulAction.orbit C s) := by exact fun s => Fintype.ofFinite ↑(MulAction.orbit C s)
  --Con hOfinito Lean ya sabe que la orbita Cs es finita
  

  have hipotesis_p_div (s:S): Fintype.card (MulAction.orbit C s) ∣  n := by sorry
    --exact card_orbita C S n n_prime n_no_zero  --Aqui podemos aplicar la proposicion que hemos definido pero pero persiste el problema en el que no he definido la accion del grupo
  
  --Paso 5: Mostramos que existe Orb_C(s) tal que |Orb_C(s)| = 1

  have h_p_o_1 : ∀ s:S, Fintype.card (MulAction.orbit C s) = p.natAbs ∨ Fintype.card (MulAction.orbit C s) = 1 := by sorry

  have h_existe_card_1 : ∃ s:S, Fintype.card (MulAction.orbit C s) = 1 := by sorry --Aqui hay que desarrollar un razonamiento por absurdo

  --Paso 6 Final: Mostramos que como ∃ s:S tal que |Orb_C(s)| = 1, entonces existe x ∈ G tal que x^p = 1
  have hfinal: ∃ g:G, orderOf g = p.natAbs := by sorry
  exact hfinal