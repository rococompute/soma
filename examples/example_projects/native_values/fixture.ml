let now=ref(fun()->17.)
let calls=ref 0
let compute()=incr calls;!calls
