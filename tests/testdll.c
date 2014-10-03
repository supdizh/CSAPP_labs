#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>


 int main(int argc,char **argv){
 	if(execve("/bin/ls",argv,environ)<0){
 		printf("error = %d\n",errno);
 		perror("say ");
 	}
 	return 0;
 }