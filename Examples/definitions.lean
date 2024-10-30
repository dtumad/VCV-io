import VCVio
import Init

def generate_nonce : String :=
  "nonce"

structure Context where
  sender_id : String
  recipient_id : String
  timestamp : String
  message_id : String
  deriving Repr

structure FrankingTag where
  tag : String
  deriving Repr

structure ReportingTag where
  tag : String
  deriving Repr

def hmac_sha256 (key : String) (data : String) : String :=
  s!"HMAC_SHA256({key}, {data})"

def serialize (msg : String) (nonce : String) : String :=
  s!"({msg}||{nonce})"

def context_to_string (context : Context) : String :=
  s!"C({context.sender_id},{context.recipient_id},{context.timestamp},{context.message_id})"

-- T_F = HMAC_SHA256(N_F, M)
def generate_franking_tag (msg : String) : (FrankingTag) :=
  let nonce := generate_nonce
  let string_M := serialize msg nonce
  let franking_tag := hmac_sha256 nonce string_M
  { tag := franking_tag }

-- R_F = HMAC_SHA256(K_F, T_F || context)
def generate_reporting_tag (franking_tag : FrankingTag) (context : Context) (facebook_key : String) : ReportingTag :=
  let franking_and_context := serialize franking_tag.tag (context_to_string context)
  let reporting_tag := hmac_sha256 facebook_key franking_and_context
  { tag := reporting_tag }

def main : IO Unit := do
  let franking_tag := generate_franking_tag "message"
  IO.println s!"Franking Tag: {franking_tag.tag}"
  let context := {
    sender_id := "alice",
    recipient_id := "bob",
    timestamp := "1730230302",
    message_id := "msg123"
  }
  let facebook_key := "facebook_key"
  let reporting_tag := generate_reporting_tag franking_tag context facebook_key
  IO.println s!"\nReporting Tag: {reporting_tag.tag}"

#eval main
