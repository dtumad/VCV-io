
import LibSodium

def main : IO Unit := do
  IO.println <| "Thanks for running me!"
  -- Test running an externally defined function
  IO.println <| "Running an external addition of 1 + 1:"
  IO.println <| myAdd 1 1
