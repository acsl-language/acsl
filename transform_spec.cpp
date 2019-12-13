/*@ behavior model:
  requires \valid(first1,last1) && \valid(result + (0.. last1-first1));
  {
    InputIterator in = first1; 
    OutputIterator out = result;
    /@
     loop_invariant 0 <= \count <= last1-first1;; 
     loop_invariant in == first1 + \count;
     loop_invariant out = result + \count;
     loop_modifies out[0 .. last1-first1-1];
     loop_decreases (last1 - first1) - \count;
     @/
     while (in != last1) {
      ... effect of op ...
     ++in;
     ++out;
    }
  }
@*/
template <class InputIterator, class OutputIterator, class UnaryOperator>
OutputIterator transform (InputIterator first1, InputIterator last1,
                          OutputIterator result, UnaryOperator op);
