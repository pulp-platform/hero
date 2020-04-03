#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>



int main(){
	
	long ws = N; 
	char* buf = malloc(ws);
	char* buf_dest = malloc(ws);
	
	memset(buf, '0', ws);
	memset(buf_dest, '1', ws);

	while(1){
		memcpy(buf_dest, buf, ws);
	}
	
	free(buf);
	free(buf_dest);
	
return 0;
}
