require import AllCore List IntDiv.
require import Array4.
require import Curve25519_ref4.
from Jasmin require import JModel.

op touches (m m' : global_mem_t) (p : address) (len : int) =
    forall i, !(0 <= i < len) => m'.[p + i] = m.[p + i].


   
module T = {
    proc load(p:W64.t): W64.t Array4.t = 
    {
        return load_array4(Glob.mem, 
    } 

}   
   
equiv eq_load_array: load_array ~ M.__load4:
    true ==> true.
proof.
admit.
qed.
