#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

int main(){
	
		
	srand(time(NULL));
	long ws = N; 

	int bytes = 64;
	int i_src, i_dst;
	char* buf_src = malloc(sizeof(char *) * ws);
	char* buf_dest = malloc(sizeof(char *) * ws);
	
	memset(buf_src, '0', ws);
	memset(buf_dest, '1', ws);

	while(1){
		i_src = rand() % (ws - bytes);
		i_dst = rand() % (ws - bytes);
		memcpy(&buf_dest[i_dst], &buf_src[i_src], bytes * sizeof(char *));
	}
	
	free(buf_src);
	free(buf_dest);
	
return 0;
}
