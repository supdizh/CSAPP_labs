#include <unistd.h>//fork
#include <sys/types.h>//pid_t
#include <sys/wait.h> //wait pid

#include <stdio.h> //perror,printf
#include <stdlib.h> //exit

#include <errno.h> //errno

#define N 2

void unix_error(const char *msg){
	perror(msg);
	exit(1);
}

int Fork(void){
	pid_t pid;
	if((pid = fork())<0){
		unix_error("fork error");
	}
	//printf("in Fork,pid<%d> sends its regard\n",getpid());
	return pid;
}

int main(){
	int status, i ;
	pid_t pid;



	for(i = 1;i <= N;i++){
		if((pid = Fork()) == 0){
			printf("child %d of pid<%d> sends its regard\n",i,getpid());
			*(char*) main = 1;
		}
	}

	while((pid = waitpid(-1,&status,0)) > 0){
		if(WIFEXITED(status))
			printf("child %d terminated normally wit exit status = %d\n",pid,WIFEXITED(status));
		else if(WIFSIGNALED(status)){
			printf("child %d terminated by uncaught signal %d \n",pid,WTERMSIG(status));
			psignal(WTERMSIG(status),"say :");
		}
		else 
			printf("what else ? \n");
	}

	if(errno != ECHILD){
		unix_error("no child anymore");
	}
}