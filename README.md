CSAPP_labs
==========

8 labs for book "Computer System: a programmer's perspective"

1 datalab 
只用位操作完成函数，并且限制操作次数
bitCount我用了分治的方法
float_i2f的截位定义需要参考一下标准
float_twice其实是float本身设计的比较巧妙

2 bomblab
主要是熟悉gdb，程序栈和汇编代码啦，还有objdump -t/-d,strings
观察phase_defused 得知要进入secret_phase,第4关的输入即为"%d austinpowers"
我拿到的secret_phase就是分析汇编下的二叉搜索树
各种x/3w然后树的样子画出来就好


3

4

5

6 malloclab
这个做的时间最久了，从简单的explicit list 50分开始，到最后分层优化的Segregated list 98分
当然如果最后两个测试用用例采用某种恶心的方法能到100分..鉴于测试用例是可以用pl自动生成的..不采用

7 shelllab
一个简单的shell环境，没怎么做额外功能添加

8 proxylab
基本上就是书上13章的内容
用信号量搭的producer-consumer模型
3个sem分别负责buf的同步，buf余量和现有job的同步
