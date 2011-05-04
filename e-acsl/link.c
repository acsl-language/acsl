struct btree {
  int val;
  struct btree *left, *right;
};

/*@ iterator access(_, struct btree *t): 
  @   nexts t->left, t->right; 
  @   guards \valid(t->left), \valid(t->right); */

/*@ predicate is_even(struct btree *t) = 
  @   \forall struct btree *tt; access(tt, t) ==> tt->val % 2 == 0; */
