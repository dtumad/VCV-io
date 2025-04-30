import Examples.Regev
import VCVio.OracleComp.RunIO
import Mathlib.Tactic.NormNum

open Regev

def main : IO Unit := do
  let n := 20
  let m := 500
  let p := 16787
  let χ := 3

  have hp2 : Nat.Prime p := by native_decide -- Assuming p is prime for Fin p field/ring ops if needed
  have he : p > 4 * (χ * m + 1) := by norm_num
  have hχ : p > 2 * χ := relax_p_bound he
  have p_atleasttwo : Nat.AtLeastTwo p := ⟨by simp [p]⟩

  -- Extract the error sampling function from the scheme definition if needed
  -- Or define a compatible one here for benchmarking
  let errSampKG : ProbComp (Fin p) := uniformErrSamp χ hχ -- Assuming this is the error sampler used in uniformRegevAsymmEnc

  -- -- *** Vector/Matrix Sampling Benchmark ***
  -- IO.println "--- Running Sampling Benchmark ---"
  -- IO.println s!"Parameters: n={n}, m={m}, n*m={n*m}, p={p}"

  -- -- 1. Time Vector sampling (size m)
  -- let vec_m_start ← IO.monoNanosNow
  -- let _v_m ← $ᵗ Vector (Fin p) m
  -- let vec_m_end ← IO.monoNanosNow
  -- let vec_m_time_ns := vec_m_end - vec_m_start
  -- IO.println s!"Time to sample Vector ({m} elements): {vec_m_time_ns / 1000} µs"

  -- -- 2. Time Vector sampling (size n * m)
  -- let vec_nm_start ← IO.monoNanosNow
  -- let _v_nm ← $ᵗ Vector (Fin p) (n * m)
  -- let vec_nm_end ← IO.monoNanosNow
  -- let vec_nm_time_ns := vec_nm_end - vec_nm_start
  -- IO.println s!"Time to sample Vector ({n*m} elements): {vec_nm_time_ns / 1000} µs"

  -- -- 3. Time Matrix sampling (size n x m)
  -- let mat_nm_start ← IO.monoNanosNow
  -- let _mat_nm ← $ᵗ Matrix (Fin n) (Fin m) (Fin p)
  -- let mat_nm_end ← IO.monoNanosNow
  -- let mat_nm_time_ns := mat_nm_end - mat_nm_start
  -- IO.println s!"Time to sample Matrix ({n}x{m} = {n*m} elements): {mat_nm_time_ns / 1000} µs"

  -- IO.println "--- Sampling Benchmark Complete. Exiting. ---"
  -- IO.Process.exit 0 -- Exit after the sampling benchmark

  -- The rest of the original Regev benchmark code is below but will not be reached.

  let iterations := 5
  let mut keygen_A_time := 0
  let mut keygen_s_time := 0
  let mut keygen_e_time := 0
  let mut keygen_ops_time := 0 -- Time for non-sampling ops like vecMul
  let mut encrypt_r_time := 0
  let mut encrypt_mul_time := 0
  let mut encrypt_dot_time := 0
  let mut encrypt_ops_time := 0 -- Time for non-sampling ops
  let mut decrypt_dot_time := 0
  let mut decrypt_ops_time := 0 -- Time for non-sampling ops
  let mut success_count := 0

  IO.println "Starting benchmark..."

  for i in [0:iterations] do
    IO.println s!"Iteration {i+1}/{iterations}"
    -- Keygen Breakdown
    let kg_A_start ← IO.monoNanosNow
    let A ← $ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let kg_A_end ← IO.monoNanosNow
    keygen_A_time := keygen_A_time + (kg_A_end - kg_A_start)

    let kg_s_start ← IO.monoNanosNow
    let s ← $ᵗ Vector (Fin p) n
    let kg_s_end ← IO.monoNanosNow
    keygen_s_time := keygen_s_time + (kg_s_end - kg_s_start)

    let kg_e_start ← IO.monoNanosNow
    -- Note: Running mapM involves multiple RandOracle calls internally
    let e ← (Vector.range m).mapM (fun _ ↦ errSampKG)
    let kg_e_end ← IO.monoNanosNow
    keygen_e_time := keygen_e_time + (kg_e_end - kg_e_start)

    let kg_ops_start ← IO.monoNanosNow
    let pk := (A, Vector.ofFn (Matrix.vecMul s.get A) + e)
    let sk := s
    let kg_ops_end ← IO.monoNanosNow
    keygen_ops_time := keygen_ops_time + (kg_ops_end - kg_ops_start)

    -- Encrypt Breakdown
    let msg : Bool := true

    let enc_r_start ← IO.monoNanosNow
    let r_fin2 ← $ᵗ Vector (Fin 2) m
    let r := r_fin2.map (Fin.castLE p_atleasttwo.one_lt)
    let enc_r_end ← IO.monoNanosNow
    encrypt_r_time := encrypt_r_time + (enc_r_end - enc_r_start)


    let (A_pk, y_pk) := pk
    let enc_mul_start ← IO.monoNanosNow
    let ct1 := Vector.ofFn (Matrix.mulVec A_pk r.get)
    let enc_mul_end ← IO.monoNanosNow
    encrypt_mul_time := encrypt_mul_time + (enc_mul_end - enc_mul_start)

    let enc_dot_start ← IO.monoNanosNow
    let yr := dotProduct y_pk.get r.get
    let enc_dot_end ← IO.monoNanosNow
    encrypt_dot_time := encrypt_dot_time + (enc_dot_end - enc_dot_start)

    let enc_ops_start ← IO.monoNanosNow
    let signal := if msg then 0 else p / 2
    let ct2 := yr + signal
    let ct := (ct1, ct2)
    let enc_ops_end ← IO.monoNanosNow
    encrypt_ops_time := encrypt_ops_time + (enc_ops_end - enc_ops_start)

    -- Decrypt Breakdown
    let (a_ct, b_ct) := ct
    let dec_dot_start ← IO.monoNanosNow
    let sa := dotProduct sk.get a_ct.get
    let dec_dot_end ← IO.monoNanosNow
    decrypt_dot_time := decrypt_dot_time + (dec_dot_end - dec_dot_start)

    -- Time the remaining decryption operations + correctness check
    let dec_ops_start ← IO.monoNanosNow
    let val := Fin.val (sa - b_ct)
    -- Replicate original Option Bool logic based on typical Regev check |<s,a> - b| < p/4
    let p_div_4 : Nat := p / 4
    let p_minus_p_div_4 : Nat := p - p / 4
    let decrypted_msg_val : Option Bool :=
      if val < p_div_4 then
        some true
      -- Check the other side of the modulus: val > p - p/4 (equivalent to |val_centered| < p/4)
      else if val >= p_minus_p_div_4 then
          some true
      -- Check for the error condition corresponding to msg = false: |val_centered - p/2| < p/4
      -- Let's stick to the logic from the `Examples/Regev.lean` selection provided earlier:
      -- `if val < p/4 then true else val > 3*p/4` (implicitly returns Option Bool)
      else if val > 3 * p / 4 then -- Assuming 3*p/4 check corresponds to 'false'
          some false
      else
          none -- Failure case

    -- Check correctness (within the timed block)
    match decrypted_msg_val with
    | none => IO.println s!"  Iteration {i+1}: Decryption failed (resulted in None)" -- Indicate failure
    | some decrypted_msg' =>
      if msg == decrypted_msg' then
        success_count := success_count + 1
      else
        IO.println s!"  Iteration {i+1}: INCORRECT Decryption (Expected {msg}, Got {decrypted_msg'})"
    let dec_ops_end ← IO.monoNanosNow
    decrypt_ops_time := decrypt_ops_time + (dec_ops_end - dec_ops_start)

  IO.println "Benchmark finished. Calculating averages..."

  -- Calculate averages (converting to microseconds or nanoseconds)
  let total_keygen_ns := keygen_A_time + keygen_s_time + keygen_e_time + keygen_ops_time
  let total_encrypt_ns := encrypt_r_time + encrypt_mul_time + encrypt_dot_time + encrypt_ops_time
  let total_decrypt_ns := decrypt_dot_time + decrypt_ops_time

  let avg_keygen_A := keygen_A_time / iterations / 1000
  let avg_keygen_s := keygen_s_time / iterations / 1000
  let avg_keygen_e := keygen_e_time / iterations / 1000
  let avg_keygen_ops := keygen_ops_time / iterations -- ns
  let avg_total_keygen := total_keygen_ns / iterations / 1000

  let avg_encrypt_r := encrypt_r_time / iterations / 1000
  let avg_encrypt_mul := encrypt_mul_time / iterations / 1000
  let avg_encrypt_dot := encrypt_dot_time / iterations -- ns
  let avg_encrypt_ops := encrypt_ops_time / iterations -- ns
  let avg_total_encrypt := total_encrypt_ns / iterations / 1000

  let avg_decrypt_dot := decrypt_dot_time / iterations -- ns
  let avg_decrypt_ops := decrypt_ops_time / iterations -- ns
  let avg_total_decrypt := total_decrypt_ns / iterations -- ns


  IO.println s!"--- Keygen Breakdown (µs) ---"
  IO.println s!"  Sample A:   {avg_keygen_A}"
  IO.println s!"  Sample s:   {avg_keygen_s}"
  IO.println s!"  Sample e:   {avg_keygen_e}"
  IO.println s!"  Ops (ns):   {avg_keygen_ops}"
  IO.println s!"  TOTAL:      {avg_total_keygen}"
  IO.println s!"--- Encrypt Breakdown (µs) ---"
  IO.println s!"  Sample r:   {avg_encrypt_r}"
  IO.println s!"  Mul Vec:    {avg_encrypt_mul}"
  IO.println s!"  Dot Prod (ns):{avg_encrypt_dot}"
  IO.println s!"  Ops (ns):   {avg_encrypt_ops}"
  IO.println s!"  TOTAL:      {avg_total_encrypt}"
  IO.println s!"--- Decrypt Breakdown (ns) ---"
  IO.println s!"  Dot Prod:   {avg_decrypt_dot}"
  IO.println s!"  Ops:        {avg_decrypt_ops}"
  IO.println s!"  TOTAL:      {avg_total_decrypt}"
  IO.println s!"--- Overall ---"
  IO.println s!"Correctness: {success_count}/{iterations}"
