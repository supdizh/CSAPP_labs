/*
 * proxy.c - CS:APP Web proxy
 *
 * TEAM MEMBERS:
 * supdizh superdizh@gmail.com
 * 
 * IMPORTANT: Give a high level description of your code here. You
 * must also provide a header comment at the beginning of each
 * function that describes what that function does.
 */ 

#include "csapp.h"

#define PORT 8087
#define NTHREAD 8
#define SBUFSIZE 64

 typedef struct{
    int clientfd;
    struct sockaddr_in clientaddr;
 }client_info; //assigned to threads as client info

typedef struct{
    client_info **buf;
    int n;
    int front;
    int rear;
    sem_t mutex;
    sem_t slots;
    sem_t items;
}sbuf_t;//producer-consumer model buffer for proxy

void sbuf_init(sbuf_t *sp, int n);
void sbuf_deinit(sbuf_t *sp);
void sbuf_insert(sbuf_t *sp, client_info *client);
client_info *sbuf_remove(sbuf_t *sp);


/*
 * Function prototypes
 */
 int parse_uri(char *uri, char *target_addr, char *path, int  *port);
 void format_log_entry(char *logstring, struct sockaddr_in *sockaddr, char *uri, int size);
 int open_clientfd_ts(char *hostname, int port);;
 void clienterror(int fd,char *cause, char *errnum, char *shortmsg, char *longmsg);

//read /write socket
 ssize_t Rio_readlineb_w(rio_t *rp, void *usrbuf, size_t maxlen);
 void Rio_writen_w(int fd, void *usrbuf, size_t n);

//thread and doproxy
 void *thread(void *vargp);//vargp = vara parameter
 void *doproxy(client_info *client,int ThreadID);

 //global variables
 sem_t log_mutex,gethost_mutex;
 sbuf_t sbuf;


/* 
 * main - Main routine for the proxy program 
 */
 int main(int argc, char **argv)
 {
    int port,  listenfd ,i;
    socklen_t clientlen;

    struct sockaddr_in client_addr;
    client_info *client;
    pthread_t tid;
    signal(SIGPIPE,SIG_IGN);
    clientlen = sizeof(client_addr);
	/* Check arguments */
	if (argc != 2) {
		fprintf(stderr, "Usage: %s <port number>\n", argv[0]);
		exit(0);
	}
    port = atoi(argv[1]);
    Sem_init(&log_mutex, 0, 1);
    Sem_init(&gethost_mutex, 0, 1);
    sbuf_init(&sbuf, SBUFSIZE);


    listenfd = open_listenfd(port);
    //starting the threads here
    for(i = 0; i < NTHREAD; i++)
          Pthread_create(&tid, NULL, thread, NULL);

    while(1){
        client = (client_info *)malloc(sizeof(client_info));
        client->clientfd = Accept(listenfd, (SA *)&(client->clientaddr), &clientlen);
        sbuf_insert(&sbuf,client);
    }
	exit(0);
}

void *thread(void *vargp){
    static int cnt = 1;
    Pthread_detach(pthread_self());
    int threadID = cnt++;
    //printf("thread[%d]\n", cnt++);
    while(1){
        client_info *client = sbuf_remove(&sbuf);
        printf("thread[%d] handling client %d\n",threadID,client->clientfd);
        doproxy(client,threadID);
    }
    return NULL;
}

void *doproxy(client_info *client,int threadID){
    char temp[MAXLINE], method[10], uri[MAXLINE], version[10], toHost[MAXLINE], logBuf[MAXLINE], toClient[MAXLINE];
    char hostName[MAXLINE],pathName[MAXLINE];
    int port, clientfd, hostfd, logfd, n, cnt = 0;
    rio_t clientRio,hostRio;
    struct sockaddr_in clientaddr;
    clientfd = client->clientfd;
    clientaddr = client->clientaddr;
    Free(client);//no futher usage
    Rio_readinitb(&clientRio, clientfd);
    if(Rio_readlineb_w(&clientRio, temp, MAXLINE) == 0)
        return NULL;
    sscanf(temp,"%s %s %s", method, uri, version);
    if(strcasecmp(method,"GET")){
        clienterror(clientfd, method, "501", "Not Implement", "proxy does not implenment this method");
        Close(clientfd);
        return NULL;
    }
    parse_uri(uri, hostName, pathName, &port);
    printf("hostName:%s\npathName:%s\nport:%d\n",hostName, pathName, port);

    if((hostfd = open_clientfd_ts(hostName, port)) < 0){
        sprintf(toClient,"open_clientfd_ts fail");
        printf("to client:%s\n",toClient);
        //should I use clienterror? seems not a host response
        Rio_writen_w(clientfd,toClient,strlen(toClient));
        Close(clientfd);
        return NULL;
    }
    printf("Host connected,formatting messages to host\n");
    sprintf(toHost,"%s %s %s\r\n",method,pathName,version);
    printf("header:%s\r\n",toHost);
    //and the following requests
    while(strcmp(temp,"\r\n")){
        bzero(temp,MAXLINE);
        Rio_readlineb_w(&clientRio, temp, MAXLINE);
        sprintf(toHost,"%s%s",toHost,temp);
        printf("%s",temp);
    }
    printf("forwarding request from client to host\n");
    Rio_writen_w(hostfd,toHost,sizeof(toHost));

    Rio_readinitb(&hostRio,hostfd);
    printf("reading reply from host and fowarding to client\n");
    bzero(temp,MAXLINE);
    while((n = Rio_readlineb_w(&hostRio, temp, MAXLINE)) > 0){
        printf("reply:%s",temp);
        Rio_writen_w(clientfd, temp, n);
        cnt += n;
        bzero(temp,MAXLINE);
    }
    fflush(stdout);
    printf("cnt:%d\n",cnt);
    format_log_entry(logBuf, &clientaddr, uri, cnt);
    printf("Logging\n%s\n",logBuf);
    P(&log_mutex);
    logfd = Open("proxy.log", O_APPEND | O_WRONLY, S_IWUSR);
    Rio_writen(logfd, logBuf,strlen(logBuf));
    Close(logfd);
    V(&log_mutex);
    printf("clsing client and host sock\n");
    Close(clientfd);
    Close(hostfd);
    return NULL;
}


/*
 * parse_uri - URI parser
 * 
 * Given a URI from an HTTP proxy GET request (i.e., a URL), extract
 * the host name, path name, and port.  The memory for hostname and
 * pathname must already be allocated and should be at least MAXLINE
 * bytes. Return -1 if there are any problems.
 */
 int parse_uri(char *uri, char *hostname, char *pathname, int *port)
 {
	char *hostbegin;
	char *hostend;
	char *pathbegin;
	int len;

	if (strncasecmp(uri, "http://", 7) != 0) {
		 hostname[0] = '\0';
		 return -1;
 }

		/* Extract the host name */
 hostbegin = uri + 7;
 hostend = strpbrk(hostbegin, " :/\r\n\0");
 len = hostend - hostbegin;
 strncpy(hostname, hostbegin, len);
 hostname[len] = '\0';

		/* Extract the port number */
		*port = 80; /* default */
 if (*hostend == ':')   
		 *port = atoi(hostend + 1);

		/* Extract the path */
 pathbegin = strchr(hostbegin, '/');
 if (pathbegin == NULL) {
		 pathname[0] = '\0';
 }
 else {
		 strcpy(pathname, pathbegin);
 }

 return 0;
}

/*
 * format_log_entry - Create a formatted log entry in logstring. 
 * 
 * The inputs are the socket address of the requesting client
 * (sockaddr), the URI from the request (uri), and the size in bytes
 * of the response from the server (size).
 */
 void format_log_entry(char *logstring, struct sockaddr_in *sockaddr, 
	char *uri, int size)
 {
	time_t now;
	char time_str[MAXLINE];
	unsigned long host;
	unsigned char a, b, c, d;
    int port;

		/* Get a formatted time string */
	now = time(NULL);
	strftime(time_str, MAXLINE, "%a %d %b %Y %H:%M:%S %Z", localtime(&now));

		/* 
		 * Convert the IP address in network byte order to dotted decimal
		 * form. Note that we could have used inet_ntoa, but chose not to
		 * because inet_ntoa is a Class 3 thread unsafe function that
		 * returns a pointer to a static variable (Ch 13, CS:APP).
		 */
		 host = ntohl(sockaddr->sin_addr.s_addr);
		 a = host >> 24;
		 b = (host >> 16) & 0xff;
		 c = (host >> 8) & 0xff;
		 d = host & 0xff;

         port = ntohs(sockaddr->sin_port);
		/* Return the formatted log entry string */
		 sprintf(logstring, "%s: %d.%d.%d.%d:%d %s %d\n", time_str, a, b, c, d,port, uri, size);
 }


int open_clientfd_ts(char *hostname,int port){
    int clientfd;
    struct hostent *hp;
    struct sockaddr_in serveraddr;
    if((clientfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        return -1;
    bzero((char *)&serveraddr,sizeof(serveraddr));
    serveraddr.sin_family = AF_INET;
    P(&gethost_mutex);
    if((hp = gethostbyname(hostname)) == NULL)
        return -2;
    bcopy((char *)hp->h_addr_list[0],(char *)&serveraddr.sin_addr.s_addr, hp->h_length);
    V(&gethost_mutex);
    serveraddr.sin_port = htons(port);
    if(connect(clientfd, (SA *)&serveraddr, sizeof(serveraddr)) < 0)
        return -1;
    return clientfd;
}


/*
 * clienterror - returns an error message to the client
 * when error occurs at the proxy
 */
void clienterror(int fd, char *cause, char *errnum, 
         char *shortmsg, char *longmsg) 
{
    char buf[MAXLINE], body[MAXBUF];

    /* Build the HTTP response body */
    sprintf(body, "<html><title>Tiny Error</title>");
    sprintf(body, "%s<body bgcolor=""ffffff"">\r\n", body);
    sprintf(body, "%s%s: %s\r\n", body, errnum, shortmsg);
    sprintf(body, "%s<p>%s: %s\r\n", body, longmsg, cause);
    sprintf(body, "%s<hr><em>The Tiny Web server</em>\r\n", body);

    /* Print the HTTP response */
    sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-type: text/html\r\n");
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
    Rio_writen(fd, buf, strlen(buf));
    Rio_writen(fd, body, strlen(body));
}


void Rio_writen_w(int fd, void *usrbuf, size_t n) 
{
    if (rio_writen(fd, usrbuf, n) != n)
  
       printf("Rio_writen_w error");
    
}

ssize_t Rio_readlineb_w(rio_t *rp, void *usrbuf, size_t maxlen) 
{
    ssize_t rc;
    rc = rio_readlineb(rp, usrbuf, maxlen);
    return rc;
}


void sbuf_init(sbuf_t *sp, int n)
{
     sp->buf = Calloc(n,sizeof(client_info *));
     sp->n = n;
     sp->front = sp->rear = 0;
     Sem_init(&sp->mutex, 0, 1);
     Sem_init(&sp->slots, 0, n);
     Sem_init(&sp->items, 0, 0);
}
void sbuf_deinit(sbuf_t *sp)
{
     Free(sp->buf);
}
void sbuf_insert(sbuf_t *sp, client_info *item)
{
     P(&sp->slots);
     P(&sp->mutex);
     sp->buf[(++sp->rear)%(sp->n)] = item;
     V(&sp->mutex);
     V(&sp->items);
}
client_info *sbuf_remove(sbuf_t *sp)
{
     client_info *item;
     P(&sp->items);
     P(&sp->mutex);
     item = sp->buf[(++sp->front)%(sp->n)];
     V(&sp->mutex);
     V(&sp->slots);
     return item;
}