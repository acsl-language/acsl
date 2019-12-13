/*@
  requires \valid(first1,last1) && \valid(result,result + (0.. last1-first1-1));
  {
    InputIterator in = first1;
    OutputIterator out = result;
    /@
       loop invariant 0 <= \count <= last1-first1;
       loop invariant in == first1 + \count;
       loop invariant out = result + \count;
       loop assigns out[0 .. last1-first1-1],
                    \union(int i = 0 .. \count-1; \assigns(op,in[i]));
       loop decreases (last1 - first1) - \count;
     @/
     while (in != last1) {
       int temp_arg = *in;
       assert \pre(op,temp_arg);
       havoc \assigns(op,temp_arg);
       int temp_result;
       assume \post(op,temp_result,temp_arg);
       *out = temp_result;
       ++in;
       ++out;
     }
  }
  @*/
template <class InputIterator, class OutputIterator, class UnaryOperator>
OutputIterator transform (InputIterator first1, InputIterator last1,
                          OutputIterator result, UnaryOperator op);
