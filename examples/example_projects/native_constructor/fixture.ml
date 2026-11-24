type table=(string,string)Hashtbl.t
type kind=Empty|Name of string|Pair of string*string|Triple of string*string*string|Inline of {mutable text:string}|Directory of table
let make()=Name "native constructor"
