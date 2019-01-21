typedef bool (*BI)(int);

/*@
requires valid_iterator_range(begin,end);
requires \requires(fp,_);
requires \assigns{_}(fp,_) <:= \empty;
assigns \empty;
ensures \result <==> (\forall int i; 0 <= i < (end-begin) ==> 
                                  (\forall bool b; b <==> \ensures(fp,b,*(begin+i))));
@*/
ensures \result ==
bool all_of(const int* begin, const int* end, BI fp) {
    ...
}

/*@
requires 0 <= begin <= end <= length(a);
assigns \empty;
ensures (\forall int i; begin<=i<end ==> (\forall bool b; b <==> ensures(fp,b,a[i])));
@*/
void test(const int a[], int begin, int end, BI fp) {
   bool b = all_of(&a[begin], &a[end], fp);
   //@ assert b;
}



