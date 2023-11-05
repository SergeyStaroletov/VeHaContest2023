/* (and (integer-listp a) (natp n) (< 0 n) (<= n (length a))) */
int element_equality(int *a, int n){
    int result = 1;
    for (int i = 1; i < n; i++)
	{
        if (a[i-1] != a[i])
		{
		    result = 0;
			break;
		}
	}
    return result;
}
/* (= (element-equality 0 (- n 1) a) result) */
