function brace_delta(text, copy, opens, closes) {
  copy = text
  opens = gsub(/\{/, "", copy)
  copy = text
  closes = gsub(/\}/, "", copy)
  return opens - closes
}

function is_create(text) {
  return text ~ /pthread_create[[:space:]]*\(/ &&
         text !~ /^[[:space:]]*extern/
}

BEGIN {
  in_loop = 0
  awaiting_body = 0
  depth = 0
  loop_creates = 0
}

{
  if(in_loop) {
    if(is_create($0))
      loop_creates++
    depth += brace_delta($0)
    if(depth <= 0)
      in_loop = 0
    next
  }

  if(awaiting_body) {
    if(is_create($0))
      loop_creates++
    delta = brace_delta($0)
    if(delta > 0) {
      in_loop = 1
      depth = delta
    }
    awaiting_body = 0
    next
  }

  if($0 ~ /(^|[^[:alnum:]_])while[[:space:]]*\(/) {
    if(is_create($0))
      loop_creates++
    delta = brace_delta($0)
    if(delta > 0) {
      in_loop = 1
      depth = delta
    }
    else if(!is_create($0))
      awaiting_body = 1
  }
}

END {
  exit loop_creates == 1 ? 0 : 1
}
