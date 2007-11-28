/*@ // src and dest cannot overlap
  @ requires \base_addr(src) != \base_addr(dest); 
  @ // src is a valid C string
  @ requires \strlen(src) >= 0 ; 
  @ // dest is large enough to store a copy of src up to the 0
  @ requires \valid_range(dest,0,\strlen(src)); 
  @ ensures
  @   \forall integer k; 0 <= k <= \strlen(src) ==> dest[k] == src[k]
  @*/
void str_cpy(char *dest, const char *src);


