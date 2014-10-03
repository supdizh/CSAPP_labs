#include <stdio.h>
#include <unistd.h>

extern char **environ;

int main(int argc,char *argv[],char *envp[]){
	int i;

	for(i=0;environ[i]!=NULL;i++)
		printf("environ[%2d]: %s\n",i,environ[i]);


}