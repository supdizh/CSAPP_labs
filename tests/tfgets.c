#include <unistd.h>//fork
#include <sys/types.h>//pid_t
#include <sys/wait.h> //wait pid

#include <stdio.h> //perror,printf
#include <stdlib.h> //exit

#include <setjmp.h> // sigjumps


#define MAXLINE 100

static sigjmp_buf env;


static void handler(int sig){
	alarm(0);
	siglongjmp(env, 1);
}

char *tfgets(char *s, int size, FILE *stream){	
	signal(SIGALRM, handler);
	alarm(2);
	if (sigsetjmp(env, 1) == 0)
		return(fgets(s, size, stream));
	else 
		return NULL; /* return NULL if fgets times out */
}

int main(){
	char buf[MAXLINE];

	while (1) {
		if (tfgets(buf, sizeof(buf), stdin) != NULL)
			printf("read: %s", buf);
		else
			printf("timed out\n");
	}
	exit(0);
}