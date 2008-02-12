typedef int size_t;
typedef FILE;

/*@ behavior normal:
  @   post assumes \result == nmemb;
  @ behavior error:
  @   post assumes \result < nmemb ;
  @*/
size_t fwrite(const  void  *ptr,  size_t  size,  size_t  nmemb,  
	      FILE *stream);


/*@ behavior normal:
  @   post assumes \result != NULL;
  @   ensures \valid( (char*)\result + (0..size-1))
  @ behavior error:
  @   post assumes \result == NULL
  @   ensures true;
  @*/
void *malloc(size_t size);
