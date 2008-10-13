int f(int x) {
  
  while (x > 0) {
    
    /*@ breaks x % 11 == 0 && x == \old(x);
      @ continues (x+1) % 11 != 0 && x % 7 == 0 && x == \old(x)-1; 
      @ returns (\result+2) % 11 != 0 && (\result+1) % 7 != 0 
      @         && \result % 5 == 0 && \result == \old(x)-2;
      @ ensures (x+3) % 11 != 0 && (x+2) % 7 != 0 && (x+1) % 5 != 0
      @         && x == \old(x)-3;
      @*/
    {
      if (x % 11 == 0) break;
      x--;
      if (x % 7 == 0) continue;
      x--;
      if (x % 5 == 0) return x;
      x--;
    }
  }
  return x;
}
