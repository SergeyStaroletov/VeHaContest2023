The solution is mostly analogous to the given example about abs-sum. Post-condition states the new function to be applied to lower and higher bounds of an array and the array itself. Then the result of this application is asserted to be equal to the result of the verificated program.

Since the recursive step of the function is going from higher array bound to the lower one, and also because the body of the function refers to a value at (<lower> - 1) index, the post-condition's lower boundary is set to the second element (the one at index 1).

The function definition itself quite literally mirrors the respective definition given in C: in a non-standard situation (such as when the array bounds are not naturals or when the lower bound is greater than the higher) we return 0, a negative answer. In the base case we return 1, and otherwise we check if current highest element is equal to the one coming before it. If not, we return 0 immediately, otherwise the recursive step comes.
