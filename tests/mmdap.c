#include <stdio.h>
#include <fcntl.h>//open
#include <sys/mman.h> //memory manage
#include <stdlib.h> //exit

int main(int argc,char **argv){
	int fd;
	char *buf;
	fd = open("target.txt",O_RDWR,0);
	buf = (char*)mmap(NULL,512,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
	buf[0] = 'J';
	exit(0);
}