# xml-translator
使用智谱AI
可以翻译XML文档中的PARAC、TITLEC、或者<parac id="A-C4E6C8F0ACC6996545E558177F84DCEC">这种标签内容
本地翻译库匹配的是PARA、TITLE的内容，然后替代PARAC、TITLEC的内容
标签内的其他标签一般是保持不变
对于标签内含有其他标签的情况，只能将其他标签的前后内容分别翻译，还未解决
可以识别sdltm 格式的翻译库
可以进行多线程快速匹配
其他详见代码备注
