#include <unistd.h>//fork execve environ
#include <sys/types.h>//pid_t
#include <sys/wait.h> //wait pid

#include <stdio.h> //perror,printf
#include <stdlib.h> //exit

#include <errno.h> //errno

extern char **environ;

static void almhandler(int sig){
	alarm(0);
	printf("alarmed\n");
	alarm(3);
}

static void inthandler(int sig){
	printf("SIGINT caught, do nothing\n");
	return;
}

int mysystem(char *cmmd){
	int status;
	pid_t pid;
	signal(SIGINT, inthandler);

	if(cmmd == NULL)return -1;
	if((pid = fork())<0)return -1;

	if(pid == 0){//child
		char *argv[4]; //argv = **char
		argv[0] = "/bin/sh"; //char pointer = a string, .rodata ,pointer to const chars
		argv[1] = "-c";
		argv[2] = cmmd;
		argv[3] = NULL;//argv is "NULL terminated"
		execve(argv[0],argv,environ);
		printf("fail execve\n");
		exit(-1);
	}

	signal(SIGALRM, almhandler);
	
	alarm(3);

	while(1){
		if(pid = waitpid(-1,&status,0) < 0){ //in system call to waitpid, could signal SIGINT & SIGQUIT be caught ? seemingly not, waitpid simply fail with return <0
			if(errno != EINTR){
				printf("returning from not an interupt\n");
				return -1;
			}
		}else{
			if(WIFEXITED(status))return WEXITSTATUS(status);
			else return status;
		}
		printf("restarting wait\n");
	}
	return 0;
}

int main(){
	char command[] = "/bin/ls /home";
	mysystem(command);
	return 0;
}