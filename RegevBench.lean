import Examples.Regev
import VCVio.OracleComp.RunIO
import Mathlib.Tactic.NormNum

def main : IO Unit := do
  let n := 20
  let m := 500
  let p := 16787
  let χ := 3

  have he : p > 4 * (χ * m + 1) := by
    norm_num

  let scheme := uniformRegevAsymmEnc n m p χ he

  let iterations := 10
  let mut keygen_time := 0
  let mut encrypt_time := 0
  let mut decrypt_time := 0
  let mut success_count := 0

  for _ in [0:iterations] do
    -- Measure keygen time
    let keygen_start ← IO.monoNanosNow
    let (pk, sk) ← scheme.keygen
    let keygen_end ← IO.monoNanosNow
    keygen_time := keygen_time + (keygen_end - keygen_start)

    -- Measure encrypt time
    let msg : Bool := true
    let encrypt_start ← IO.monoNanosNow
    let ct ← scheme.encrypt pk msg
    let encrypt_end ← IO.monoNanosNow
    encrypt_time := encrypt_time + (encrypt_end - encrypt_start)

    -- Measure decrypt time
    let decrypt_start ← IO.monoNanosNow
    let decrypted_msg ← pure (scheme.decrypt sk ct)
    let decrypt_end ← IO.monoNanosNow
    decrypt_time := decrypt_time + (decrypt_end - decrypt_start)

    -- Check correctness
    match decrypted_msg with
    | none => pure ()
    | some decrypted_msg =>
      if msg == decrypted_msg then
        success_count := success_count + 1

  -- Calculate averages (converting to microseconds)
  let avg_keygen := keygen_time / iterations / 1000
  let avg_encrypt := encrypt_time / iterations / 1000
  let avg_decrypt := decrypt_time / iterations

  IO.println s!"Average .keygen Time: {avg_keygen} µs"
  IO.println s!"Average .encrypt Time: {avg_encrypt} µs"
  IO.println s!"Average .decrypt Time: {avg_decrypt} ns"
  IO.println s!"Correctness: {success_count}/{iterations}"
