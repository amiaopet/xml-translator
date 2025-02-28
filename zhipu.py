import sqlite3
import os
import threading
import concurrent.futures
import tkinter as tk
from tkinter import messagebox, Listbox, Scrollbar, Button, Entry, Label, END, SINGLE, ttk, filedialog, Scale, IntVar, StringVar, Frame
from lxml import etree
from zhipuai import ZhipuAI
from difflib import SequenceMatcher
from PIL import Image, ImageTk
import io
import base64
import re
import time
from collections import defaultdict
import pickle
import json

# 默认API设置
DEFAULT_API_KEY = "8214957676bb41e3bea675ab9b508cad.gV4qBe1HgCKrfSYA"
# 配置文件路径
CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".xml_translator_config.json")

# 初始化腾讯混元客户端
client = None

# 初始化默认目录
directory = r'C:\trados'
xml_library_dir = r'/Users/xiaoma/Library/CloudStorage/OneDrive-个人/桌面/工卡XML'

# 创建本地翻译缓存字典，键是原文(英文)，值是翻译后的文本(中文)
translation_cache = {}

# 初始化索引结构
translation_matcher = None

# 默认最低匹配阈值（百分比）
min_match_threshold = 100

# 性能统计
perf_stats = {
    "total_time": 0,
    "match_count": 0,
    "elements_per_second": 0
}

# 保存配置到文件
def save_config():
    config = {
        "api_key": api_key_var.get() if 'api_key_var' in globals() else DEFAULT_API_KEY,
        "directory": directory,
        "xml_library_dir": xml_library_dir,
        "min_match_threshold": min_match_threshold,
        "threads": threads_var.get() if 'threads_var' in globals() else 8
    }
    try:
        with open(CONFIG_FILE, 'w') as f:
            json.dump(config, f)
        print(f"配置已保存到文件: {CONFIG_FILE}")
        return True
    except Exception as e:
        print(f"保存配置失败: {e}")
        return False

# 从文件加载配置
def load_config():
    global directory, xml_library_dir, min_match_threshold, DEFAULT_API_KEY
    if not os.path.exists(CONFIG_FILE):
        print(f"配置文件不存在: {CONFIG_FILE}")
        return False
    try:
        with open(CONFIG_FILE, 'r') as f:
            config = json.load(f)
        # 更新全局变量
        if "api_key" in config:
            DEFAULT_API_KEY = config["api_key"]
        if "directory" in config:
            directory = config["directory"]
        if "xml_library_dir" in config:
            xml_library_dir = config["xml_library_dir"]
        if "min_match_threshold" in config:
            min_match_threshold = config["min_match_threshold"]
        print("配置已从文件加载")
        return True
    except Exception as e:
        print(f"加载配置失败: {e}")
        return False

def clear_cache_and_rebuild_index():
    global translation_cache, translation_matcher
    # 清除内存中的缓存
    translation_cache = {}
    translation_matcher = None
    # 删除缓存文件
    cache_file = os.path.join(xml_library_dir, "translation_cache.pkl")
    if os.path.exists(cache_file):
        try:
            os.remove(cache_file)
            print(f"已删除缓存文件: {cache_file}")
        except Exception as e:
            print(f"删除缓存文件失败: {e}")
    # 重新加载翻译库并构建索引
    status_label.config(text="正在重新加载翻译库...")
    progress_bar['value'] = 0
    def reload_thread():
        count = load_translation_library(update_progress)
        root.after(0, lambda: status_label.config(text=f"已重新加载翻译库: {count}个条目"))
        root.after(0, lambda: progress_bar.configure(value=100))
    threading.Thread(target=reload_thread).start()
    return True

class TranslationMatcher:
    def __init__(self, translation_cache, min_match_threshold=90):
        self.translation_cache = translation_cache
        self.min_match_threshold = min_match_threshold
        self.length_index = defaultdict(set)
        self.word_index = defaultdict(set)
        self.prefix_index = defaultdict(set)
        
    def create_index(self, progress_callback=None):
        """为翻译库创建索引以加速查找"""
        print("开始创建翻译索引...")
        
        # 提取常见单词的正则表达式
        word_pattern = re.compile(r'\b\w{3,15}\b')
        
        total_items = len(self.translation_cache)
        processed = 0
        
        for source_text in self.translation_cache:
            # 长度索引
            self.length_index[len(source_text)].add(source_text)
            
            # 单词索引：为源文本中的每个单词建立索引
            if is_likely_english(source_text):
                # 只为英文文本创建单词索引
                words = word_pattern.findall(source_text.lower())
                # 选择最不常见的几个单词作为索引
                if words:
                    # 简单启发式：较长的单词往往更具有辨识度
                    words.sort(key=len, reverse=True)
                    for word in words[:1]:  # 使用前1个最长单词
                        if len(word) >= 1:  # 只索引长度>=1的单词
                            self.word_index[word].add(source_text)
                
                # 前缀索引：使用前3个字符作为索引
                if len(source_text) >= 3:
                    prefix = source_text[:3].lower()
                    self.prefix_index[prefix].add(source_text)
            
            processed += 1
            if progress_callback and processed % 1000 == 0:
                progress_callback(processed, total_items)
        
        print(f"索引创建完成，长度索引大小：{len(self.length_index)}，单词索引大小：{len(self.word_index)}，前缀索引大小：{len(self.prefix_index)}")
        if progress_callback:
            progress_callback(total_items, total_items)
    
    def find_candidates(self, text, max_candidates=1000):
        """使用索引快速查找潜在的匹配候选"""
        candidates = set()
        
        # 长度筛选：选择长度相近的文本
        text_len = len(text)
        for length in range(max(6, text_len - 10), text_len + 11):
            candidates.update(self.length_index[length])
        
        # 前缀筛选：找出前几个字符相同的文本
        prefix_candidates = set()
        if len(text) >= 3 and is_likely_english(text):
            prefix = text[:3].lower()
            if prefix in self.prefix_index:
                prefix_candidates = self.prefix_index[prefix]
        
        # 单词筛选：找出包含相同关键词的文本
        word_candidates = set()
        if is_likely_english(text):
            words = re.findall(r'\b\w{3,15}\b', text.lower())
            words.sort(key=len, reverse=True)
            
            for word in words[:3]:  # 使用前3个最长单词
                if len(word) >= 3 and word in self.word_index:
                    if not word_candidates:
                        word_candidates = self.word_index[word].copy()
                    else:
                        # 累积更多候选或取交集，取决于候选数量
                        if len(word_candidates) < 100:
                            word_candidates.update(self.word_index[word])
                        else:
                            word_candidates &= self.word_index[word]
        
        # 组合索引结果
        final_candidates = candidates
        
        # 如果前缀和单词索引都有结果，合并这些结果
        if prefix_candidates and word_candidates:
            combined = prefix_candidates & word_candidates
            if combined:
                # 如果交集非空，使用交集（更精确）
                final_candidates = final_candidates & combined if final_candidates else combined
            else:
                # 否则使用并集（更广泛）
                combined = prefix_candidates | word_candidates
                final_candidates = final_candidates & combined if final_candidates else combined
        elif prefix_candidates:
            final_candidates = final_candidates & prefix_candidates if final_candidates else prefix_candidates
        elif word_candidates:
            final_candidates = final_candidates & word_candidates if final_candidates else word_candidates
        
        # 限制候选数量
        if len(final_candidates) > max_candidates:
            return list(final_candidates)[:max_candidates]
        
        return final_candidates
    
    def find_best_match(self, text):
        """查找最佳匹配的翻译"""
        if not text or len(text.strip()) <= 1:
            return None, 0
        
        text = text.strip()
        
        # 精确匹配
        if text in self.translation_cache:
            return self.translation_cache[text], 100
        
        # 使用索引获取候选
        candidates = self.find_candidates(text)
        
        # 对候选进行相似度计算
        if len(candidates) <= 50:
            # 候选较少时，单线程处理
            best_match, best_ratio = self._find_best_match_sequential(text, candidates)
        else:
            # 候选较多时，并行处理
            best_match, best_ratio = self._find_best_match_parallel(text, candidates)
        
        return best_match, best_ratio
    
    def _find_best_match_sequential(self, text, candidates):
        """串行计算相似度找出最佳匹配"""
        best_match = None
        best_ratio = 0
        
        for source_text in candidates:
            ratio = fast_similarity_ratio(text, source_text)
            if ratio > best_ratio and ratio >= self.min_match_threshold:
                best_ratio = ratio
                best_match = self.translation_cache[source_text]
        
        return best_match, best_ratio
    
    def _find_best_match_parallel(self, text, candidates, workers=4):
        """并行计算相似度找出最佳匹配"""
        # 将候选分成多个批次
        candidates_list = list(candidates)
        chunk_size = max(1, len(candidates_list) // workers)
        chunks = [candidates_list[i:i+chunk_size] for i in range(0, len(candidates_list), chunk_size)]
        
        def process_chunk(chunk):
            local_best_match = None
            local_best_ratio = 0
            for source_text in chunk:
                ratio = fast_similarity_ratio(text, source_text)
                if ratio > local_best_ratio and ratio >= self.min_match_threshold:
                    local_best_ratio = ratio
                    local_best_match = self.translation_cache[source_text]
            return local_best_match, local_best_ratio
        
        best_match = None
        best_ratio = 0
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            results = list(executor.map(process_chunk, chunks))
            
            for match, ratio in results:
                if ratio > best_ratio:
                    best_ratio = ratio
                    best_match = match
        
        return best_match, best_ratio
    
    def update_threshold(self, threshold):
        """更新匹配阈值"""
        self.min_match_threshold = threshold

def initialize_client(api_key):
    """初始化API客户端"""
    global client
    
    # 完全复制测试脚本中的成功代码
    try:
        # 清理API密钥，确保没有前后空格
        api_key = api_key.strip()
        
        print(f"尝试使用API密钥: {api_key[:5]}...{api_key[-5:] if len(api_key) > 10 else ''}")
        
        # 与测试脚本相同的方式创建客户端
        client = ZhipuAI(api_key=api_key)
        
        # 与测试脚本相同的调用方式
        response = client.chat.completions.create(
            model="glm-4-flash",
            messages=[{"role": "user", "content": "Hello, are you working?"}],
            temperature=0.7,
            max_tokens=50
        )
        
        # 如果执行到这里，说明API调用成功
        print(f"API测试成功: {response.choices[0].message.content}")
        if 'api_status_label' in globals():
            api_status_label.config(text="API状态: 已配置 (智谱AI)")
        return True
    except Exception as e:
        print(f"API测试失败: {e}")
        import traceback
        traceback.print_exc()  # 打印详细的错误堆栈
        client = None
        if 'api_status_label' in globals():
            api_status_label.config(text="API状态: 不可用(验证失败)")
        return False

def similarity_ratio(a, b):
    """计算两个字符串的相似度比例，返回0-100的整数"""
    if not a or not b:
        return 0
    return int(SequenceMatcher(None, a, b).ratio() * 100)

def fast_similarity_ratio(a, b):
    """使用快速算法计算两个字符串的相似度比例，返回0-100的整数"""
    if not a or not b:
        return 0
    
    # 如果长度差距过大，直接返回低相似度
    len_a, len_b = len(a), len(b)
    if len_a < len_b * 0.7 or len_b < len_a * 0.7:
        return 0
    
    # 首先检查前几个字符，如果差异太大就跳过详细比较
    prefix_len = min(10, min(len_a, len_b))
    if prefix_len > 5:
        prefix_match = sum(a[i].lower() == b[i].lower() for i in range(prefix_len))
        if prefix_match < prefix_len * 0.5:  # 如果前缀匹配度低于50%
            return 0
    
    # 使用SequenceMatcher进行详细比较
    return int(SequenceMatcher(None, a, b).ratio() * 100)

def load_sdltm_file(file_path, progress_callback=None):
    """从SDLTM文件(SQLite数据库)加载翻译内容到缓存，针对大型SDLTM文件优化"""
    count = 0
    
    try:
        print(f"正在加载SDLTM翻译库文件: {file_path}")
        
        # 连接到SQLite数据库
        conn = sqlite3.connect(file_path)
        cursor = conn.cursor()
        
        # 获取文件大小
        file_size_mb = os.path.getsize(file_path) / (1024 * 1024)
        print(f"SDLTM文件大小: {file_size_mb:.2f} MB")
        
        # 先尝试获取表结构
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
        tables = cursor.fetchall()
        table_names = [t[0] for t in tables]
        print(f"SDLTM文件中的表: {table_names}")
        
        # 检查具体是哪种SDLTM格式
        if 'translation_units' in table_names:
            print("检测到SDL Trados Studio格式的SDLTM文件")
            
            # 查看translation_units表的结构
            cursor.execute("PRAGMA table_info(translation_units)")
            tu_columns = [col[1] for col in cursor.fetchall()]
            print(f"translation_units表的列: {tu_columns}")
            
            # 查找ID列和文本列
            id_column = None
            source_column = None
            target_column = None
            
            # 确定列名
            for col in tu_columns:
                col_lower = col.lower()
                if 'id' in col_lower and id_column is None:
                    id_column = col
                elif ('source' in col_lower and 'segment' in col_lower) or col_lower == 'source':
                    source_column = col
                elif ('target' in col_lower and 'segment' in col_lower) or col_lower == 'target':
                    target_column = col
            
            if source_column and target_column:
                print(f"找到文本列: 源文本={source_column}, 目标文本={target_column}")
                
                # 根据SDLTM文件大小决定分批查询的大小
                batch_size = 1000 if file_size_mb < 50 else 5000
                offset = 0
                
                # 获取总记录数以用于进度更新
                cursor.execute(f"SELECT COUNT(*) FROM translation_units WHERE {source_column} IS NOT NULL AND {target_column} IS NOT NULL")
                total_records = cursor.fetchone()[0]
                processed_records = 0
                
                while True:
                    # 分批查询以处理大型文件
                    query = f"""
                    SELECT {source_column}, {target_column} 
                    FROM translation_units 
                    WHERE {source_column} IS NOT NULL AND {target_column} IS NOT NULL
                    LIMIT {batch_size} OFFSET {offset}
                    """
                    
                    cursor.execute(query)
                    batch = cursor.fetchall()
                    
                    if not batch:
                        break  # 没有更多数据
                    
                    batch_count = 0
                    for source_text, target_text in batch:
                        if source_text and target_text and isinstance(source_text, str) and isinstance(target_text, str):
                            source_text = source_text.strip()
                            target_text = target_text.strip()
                            
                            # 检查是否为有效的翻译对
                            if len(source_text) > 1 and len(target_text) > 1:
                                # 检查源文本是否为英文，确保目标文本包含中文
                                if is_likely_english(source_text) and has_chinese_characters(target_text):
                                    translation_cache[source_text] = target_text
                                    batch_count += 1
                                # 检查源文本是否为中文（翻译方向相反），确保源文本包含中文
                                elif has_chinese_characters(source_text) and is_likely_english(target_text):
                                    translation_cache[target_text] = source_text
                                    batch_count += 1
                    
                    count += batch_count
                    processed_records += len(batch)
                    
                    if progress_callback and total_records > 0:
                        progress_callback(processed_records, total_records)
                    
                    print(f"处理批次 {offset//batch_size + 1}: 添加了 {batch_count} 个翻译对，总计 {count}")
                    
                    offset += batch_size
                    
                    # 如果这批数量明显少于批处理大小，可能已接近尾声
                    if len(batch) < batch_size * 0.8:
                        break
            
            # 如果上面的方法没有提取到足够的翻译，尝试查找其他可能包含翻译的表
            if count < 100 and 'translation_unit_fragments' in table_names:
                print("尝试从translation_unit_fragments表提取翻译...")
                
                # 查看表结构
                cursor.execute("PRAGMA table_info(translation_unit_fragments)")
                tuf_columns = [col[1] for col in cursor.fetchall()]
                
                # 寻找可能包含文本的列
                text_columns = [col for col in tuf_columns if 'text' in col.lower() or 'segment' in col.lower() or 'content' in col.lower()]
                
                if text_columns and 'unit_id' in tuf_columns:
                    # 查找所有翻译单元
                    query = f"""
                    SELECT unit_id, {', '.join(text_columns)} 
                    FROM translation_unit_fragments
                    WHERE unit_id IS NOT NULL
                    """
                    
                    cursor.execute(query)
                    fragments = cursor.fetchall()
                    
                    # 按单元ID分组
                    unit_texts = {}
                    for row in fragments:
                        unit_id = row[0]
                        if unit_id not in unit_texts:
                            unit_texts[unit_id] = []
                        
                        for i in range(1, len(row)):
                            if row[i] and isinstance(row[i], str):
                                unit_texts[unit_id].append(row[i])
                    
                    # 查找每个单元中的英文和中文文本
                    fragment_count = 0
                    for unit_id, texts in unit_texts.items():
                        en_texts = []
                        zh_texts = []
                        
                        for text in texts:
                            text = text.strip()
                            if not text or len(text) <= 5:
                                continue
                            
                            if is_likely_english(text):
                                en_texts.append(text)
                            elif has_chinese_characters(text):
                                zh_texts.append(text)
                        
                        # 如果找到英文和中文文本，尝试配对
                        if en_texts and zh_texts:
                            for en_text in en_texts:
                                for zh_text in zh_texts:
                                    translation_cache[en_text] = zh_text
                                    fragment_count += 1
                    
                    if fragment_count > 0:
                        count += fragment_count
                        print(f"从fragments表添加了 {fragment_count} 个翻译对")
        
        # 如果仍未找到足够翻译，尝试使用一般方法
        if count < 100:
            print("尝试通用查询方法...")
            
            # 查找可能包含文本的表
            text_tables = []
            for table in table_names:
                try:
                    cursor.execute(f"PRAGMA table_info({table})")
                    columns = [col[1].lower() for col in cursor.fetchall()]
                    
                    # 如果表包含可能的文本列
                    text_columns = [col for col in columns if any(keyword in col for keyword in ['text', 'content', 'segment', 'source', 'target'])]
                    if len(text_columns) >= 2:  # 至少需要两列可能包含源文本和目标文本
                        text_tables.append((table, text_columns))
                except:
                    continue
            
            if text_tables:
                print(f"找到可能包含文本的表: {text_tables}")
                
                for table, columns in text_tables:
                    # 只处理尚未处理过的表
                    if table == 'translation_units' and count > 0:
                        continue
                        
                    try:
                        # 尝试查询
                        column_names = ", ".join(columns)
                        query = f"SELECT {column_names} FROM {table} LIMIT 10000"
                        
                        cursor.execute(query)
                        rows = cursor.fetchall()
                        
                        table_count = 0
                        for row in rows:
                            en_texts = []
                            zh_texts = []
                            
                            for text in row:
                                if text and isinstance(text, str):
                                    text = text.strip()
                                    if len(text) <= 5:
                                        continue
                                        
                                    if is_likely_english(text):
                                        en_texts.append(text)
                                    elif has_chinese_characters(text):
                                        zh_texts.append(text)
                            
                            # 配对英文和中文文本
                            if en_texts and zh_texts:
                                for en_text in en_texts:
                                    for zh_text in zh_texts:
                                        translation_cache[en_text] = zh_text
                                        table_count += 1
                        
                        if table_count > 0:
                            count += table_count
                            print(f"从表 {table} 添加了 {table_count} 个翻译对")
                    except sqlite3.OperationalError as e:
                        print(f"查询表 {table} 失败: {e}")
        
        # 关闭数据库连接
        cursor.close()
        conn.close()
        
        if count == 0:
            messagebox.showinfo("SDLTM加载", "未能从SDLTM文件中提取翻译。请联系开发者或尝试将SDLTM导出为TMX格式。")
        else:
            print(f"成功从SDLTM文件加载 {count} 个翻译条目")
            
    except Exception as e:
        print(f"加载SDLTM翻译库文件出错: {file_path} - {e}")
        import traceback
        traceback.print_exc()
    
    return count

# 辅助函数：检测文本是否可能为英文
def is_likely_english(text):
    # 检查是否包含大量英文字符
    if not text:
        return False
        
    # 计算英文字符比例
    english_chars = sum(1 for c in text if ('a' <= c.lower() <= 'z'))
    total_chars = len(text)
    
    # 如果英文字符比例超过50%，可能是英文
    return english_chars / total_chars > 0.5

# 辅助函数：检测文本是否包含中文字符
def has_chinese_characters(text):
    if not text:
        return False
    
    # 检查是否包含汉字
    return any('\u4e00' <= c <= '\u9fff' for c in text)

def load_translation_library(progress_callback=None):
    """从本地翻译好的XML和SDLTM文件夹加载翻译内容到缓存"""
    global translation_cache, translation_matcher
    translation_cache = {}
    
    if not os.path.exists(xml_library_dir):
        print(f"警告：翻译库目录不存在：{xml_library_dir}")
        return 0
    
    # 检查是否有缓存文件
    cache_file = os.path.join(xml_library_dir, "translation_cache.pkl")
    if os.path.exists(cache_file):
        try:
            print(f"发现翻译缓存文件，尝试加载: {cache_file}")
            with open(cache_file, 'rb') as f:
                translation_cache = pickle.load(f)
            print(f"成功从缓存加载 {len(translation_cache)} 个翻译条目")
            
            # 创建匹配器并返回
            if translation_matcher is None:
                translation_matcher = TranslationMatcher(translation_cache, min_match_threshold)
                # 创建索引
                translation_matcher.create_index(progress_callback)
            
            return len(translation_cache)
        except Exception as e:
            print(f"加载缓存失败: {e}")
            translation_cache = {}
    
    total_count = 0
    xml_count = 0
    sdltm_count = 0
    
    # 查找目录中的所有文件
    all_files = []
    for root_dir, _, files in os.walk(xml_library_dir):
        for file in files:
            file_path = os.path.join(root_dir, file)
            if file.lower().endswith('.sdltm') or file.endswith('.xml'):
                all_files.append(file_path)
    
    # 使用进度条显示总体进度
    total_files = len(all_files)
    files_processed = 0
    
    if progress_callback:
        progress_callback(0, total_files * 100)  # *100表示处理每个文件平均有100个步骤
    
    # 遍历目录中的所有文件
    for file_path in all_files:
        files_processed += 1
        file_name = os.path.basename(file_path)
        
        # 处理SDLTM文件
        if file_path.lower().endswith('.sdltm'):
            # 自定义进度回调，将单个文件的进度按比例缩放到总体进度
            def file_progress_callback(current, total):
                if progress_callback:
                    overall_progress = (files_processed - 1) * 100 + (current / total) * 100
                    progress_callback(int(overall_progress), total_files * 100)
            
            sdltm_file_count = load_sdltm_file(file_path, file_progress_callback)
            sdltm_count += sdltm_file_count
            total_count += sdltm_file_count
        
        # 处理XML文件
        elif file_path.endswith('.xml'):
            try:
                print(f"正在加载XML翻译库文件: {file_name}")
                parser = etree.XMLParser(recover=True)
                tree = etree.parse(file_path, parser)
                
                # 找出所有成对的PARAC(中文)和PARA(英文)标签
                # 1. 找出所有父元素包含PARAC和PARA的情况
                parent_elements = set()
                for elem in tree.xpath("//*[child::PARAC and child::PARA]"):
                    parent_elements.add(elem)
                
                # 处理所有找到的父元素
                for parent in parent_elements:
                    paracs = parent.xpath("./PARAC")
                    paras = parent.xpath("./PARA")
                    
                    # 确保数量一致时才配对
                    if len(paracs) == len(paras):
                        for i in range(len(paracs)):
                            if paracs[i].text and paras[i].text:
                                # 注意翻译方向：PARA是英文原文，PARAC是中文译文
                                source_text = paras[i].text.strip()
                                translated_text = paracs[i].text.strip()
                                
                                # 增加检查：目标文本必须包含至少一个中文字符
                                if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                                    # 将英文作为键，中文作为值
                                    translation_cache[source_text] = translated_text
                                    xml_count += 1
                                    total_count += 1
                
                # 2. 对于无法通过父元素找到的，使用全局的PARAC和PARA标签对
                all_paras = tree.xpath("//PARA")
                all_paracs = tree.xpath("//PARAC")
                
                # 只有在数量相等时才尝试一一对应
                if len(all_paras) == len(all_paracs):
                    for i in range(len(all_paras)):
                        if all_paras[i].text and all_paracs[i].text:
                            source_text = all_paras[i].text.strip()
                            translated_text = all_paracs[i].text.strip()
                            
                            # 增加检查：目标文本必须包含至少一个中文字符
                            if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                                # 避免重复添加
                                if source_text not in translation_cache:
                                    translation_cache[source_text] = translated_text
                                    xml_count += 1
                                    total_count += 1
                
                # 3. 特别处理：查找相邻的PARAC和PARA标签
                # 这种方法在某些情况下可能更准确
                elements = list(tree.iter())
                for i in range(len(elements) - 1):
                    current = elements[i]
                    next_elem = elements[i + 1]
                    
                    if (current.tag == 'PARAC' and next_elem.tag == 'PARA' and 
                        current.text and next_elem.text):
                        source_text = next_elem.text.strip()
                        translated_text = current.text.strip()
                        
                        # 增加检查：目标文本必须包含至少一个中文字符
                        if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                            if source_text not in translation_cache:
                                translation_cache[source_text] = translated_text
                                xml_count += 1
                                total_count += 1
                
              
                # 4. 特别处理TITLE(英文)和TITLEC(中文)配对
                title_elements = tree.xpath("//TITLE")
                titlec_elements = tree.xpath("//TITLEC")
                
                # 如果数量匹配，假设它们是一一对应的
                if len(title_elements) == len(titlec_elements):
                    for i in range(len(title_elements)):
                        if title_elements[i].text and titlec_elements[i].text:
                            source_text = title_elements[i].text.strip()
                            translated_text = titlec_elements[i].text.strip()
                            
                            # 增加检查：目标文本必须包含至少一个中文字符
                            if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                                if source_text not in translation_cache:
                                    translation_cache[source_text] = translated_text
                                    xml_count += 1
                                    total_count += 1
                
                # 5. 对于有TITLE和TITLEC子元素的父元素
                for parent in tree.xpath("//*[child::TITLE and child::TITLEC]"):
                    titles = parent.xpath("./TITLE")
                    titlecs = parent.xpath("./TITLEC")
                    
                    # 确保数量一致时才配对
                    if len(titles) == len(titlecs):
                        for i in range(len(titles)):
                            if titles[i].text and titlecs[i].text:
                                source_text = titles[i].text.strip()
                                translated_text = titlecs[i].text.strip()
                                
                                # 增加检查：目标文本必须包含至少一个中文字符
                                if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                                    if source_text not in translation_cache:
                                        translation_cache[source_text] = translated_text
                                        xml_count += 1
                                        total_count += 1

                # 6. 新增：处理PARA和PARAC内的子标签（如STDNAME）
                for parent in tree.xpath("//*[child::PARA and child::PARAC]"):
                    paras = parent.xpath("./PARA")
                    paracs = parent.xpath("./PARAC")

                    # 确保数量一致时才配对
                    if len(paras) == len(paracs):
                        for i in range(len(paras)):
                            # 检查子元素
                            para_children = list(paras[i])
                            parac_children = list(paracs[i])

                            # 如果子元素数量相同，尝试一一配对
                            if len(para_children) == len(parac_children):
                                for j in range(len(para_children)):
                                    if para_children[j].text and parac_children[j].text:
                                        source_text = para_children[j].text.strip()
                                        translated_text = parac_children[j].text.strip()

                                        # 检查是否为有效翻译对
                                        if len(source_text) > 1 and len(translated_text) > 1 and has_chinese_characters(translated_text):
                                            if source_text not in translation_cache:
                                                translation_cache[source_text] = translated_text
                                                xml_count += 1
                                                total_count += 1
                
                # 进度更新
                if progress_callback:
                    overall_progress = (files_processed * 100)
                    progress_callback(int(overall_progress), total_files * 100)
            
            except Exception as e:
                print(f"加载XML翻译库文件出错: {file_name} - {e}")
    
    print(f"已从本地翻译库加载总计 {total_count} 个翻译条目")
    print(f"其中XML文件: {xml_count} 个条目, SDLTM文件: {sdltm_count} 个条目")
    
    # 保存缓存文件以供下次使用
    try:
        cache_file = os.path.join(xml_library_dir, "translation_cache.pkl")
        with open(cache_file, 'wb') as f:
            pickle.dump(translation_cache, f)
        print(f"已保存翻译缓存到文件: {cache_file}")
    except Exception as e:
        print(f"保存翻译缓存失败: {e}")
    
    # 创建匹配器
    if total_count > 0:
        translation_matcher = TranslationMatcher(translation_cache, min_match_threshold)
        translation_matcher.create_index(progress_callback)
    
    return total_count

def find_in_local_library(text):
    """在本地翻译缓存中查找匹配项，返回(翻译文本, 匹配度)的元组"""
    global translation_matcher
    
    if not translation_matcher:
        # 如果还没有创建匹配器，使用原始方法
        if not text or len(text.strip()) <= 1:
            return None, 0
        
        text = text.strip()
        
        # 精确匹配
        if text in translation_cache:
            return translation_cache[text], 100
        
        # 模糊匹配，从高到低尝试
        best_match = None
        best_ratio = 0
        
        for source_text, translated_text in translation_cache.items():
            ratio = similarity_ratio(text, source_text)
            if ratio > best_ratio and ratio >= min_match_threshold:
                best_ratio = ratio
                best_match = translated_text
        
        if best_match:
            return best_match, best_ratio
        
        return None, 0
    else:
        # 使用优化的匹配器
        return translation_matcher.find_best_match(text)

def translate_text(text):
    global client
    
    if client is None:
        print("警告: API 客户端未初始化")
        return text
    
    try:
        # 使用智谱AI进行翻译
        completion = client.chat.completions.create(
            model="glm-4-flash",
            messages=[
                {
                    "role": "system",
                    "content": "你是一名航空工程领域的专业翻译专家，具备以下专业资质：1. 航空航天工程专业博士学位2. 10年航空技术文档翻译经验. 持有CATTI一级笔译证书4. 熟悉AS9100航空质量标准体系。翻译要求：- 使用正式书面语，禁止口语化表达- 严格遵循《航空工业术语标准》（HB 7715-2002）- 保持技术参数的绝对准确性- 采用工程文档的规范表达方式"
                },
                {
                    "role": "user",
                    "content": f"请将以下航空工程技术文本进行专业翻译，要求：1. 使用第三人称客观叙述2. 保留原始技术参数格式（如：RCS值应保持m²单位）3. 专业术语参照《英汉航空工程词典》（ISBN 978-7-118-05244-5），缩写翻译使用航空民航方向4. 句法结构符合技术文档规范(英译中)5.仅返回中文翻译结果，禁止添加任何前缀、注释或格式符号；即使原文疑似不完整，也必须直接翻译（例如let the应译为使；NRC NO翻译为NRC 号码记录），请仅输出翻译结果，仅输出翻译结果，仅输出翻译结果，不要添加任何解释性内容：{text}"
                }
            ],
            temperature=0.1,
            extra_body={
                "enable_enhancement": True,
                "terminology": {
                    "航空专用术语表": [
                        {"source": "ZONE/ACCESS", "target": "区域/接近"},
                        {"source": "Job Set-up", "target": "工作准备"},
                        {"source": "Get Access", "target": "接近"},
                        {"source": "Procedure", "target": "程序"},
                        {"source": "Close-up", "target": "结束"},
                        {"source": "（NRC No.）：", "target": "（NRC 号码记录.）："}
                        {"source": "clamp", "target": "卡箍"}
                    ]
                }
            }
        )
        return completion.choices[0].message.content.strip()
    except Exception as e:
        print(f"翻译异常: {e}")
        return text

def translate_element(elem, target_elem=None):
    """
    翻译单个 XML 元素的文本
    
    参数:
    - elem: 源元素（包含英文文本）
    - target_elem: 目标元素（如果提供则将翻译结果写入此元素，否则替换源元素文本）
    
    返回: 翻译状态和匹配度的元组
    """
    try:
        if not elem.text or len(elem.text.strip()) <= 1 or not any(c.isalpha() for c in elem.text):
            return "skip", 0
        
        # 从PARA(英文)标签中获取内容作为查询关键字
        query_text = elem.text.strip()
        
        # 记录开始时间，用于性能统计
        start_time = time.time()
        
        # 在本地库中查找匹配的中文翻译
        local_translation, match_ratio = find_in_local_library(query_text)
        
        # 计算耗时，用于性能统计
        elapsed = time.time() - start_time
        global perf_stats
        perf_stats["total_time"] += elapsed
        perf_stats["match_count"] += 1
        perf_stats["elements_per_second"] = perf_stats["match_count"] / perf_stats["total_time"] if perf_stats["total_time"] > 0 else 0
        
        if local_translation and match_ratio >= min_match_threshold:
            # 如果找到匹配，则将中文翻译应用到PARAC标签或目标元素
            if target_elem is not None:
                target_elem.text = local_translation
            else:
                elem.text = local_translation
            return "local", match_ratio
        else:
            # 本地没有找到，检查API是否可用
            if client is None:
                # API不可用，保留原值
                # 注意：这里我们不修改目标元素，保留其原有内容或默认值
                return "api_unavailable", 0
            else:
                # API可用，使用API翻译
                try:
                    translated_text = translate_text(query_text)
                    if target_elem is not None:
                        target_elem.text = translated_text
                    else:
                        elem.text = translated_text
                    return "api", 0
                except Exception as e:
                    print(f"API调用失败: {e}")
                    # API调用失败，视为API不可用
                    return "api_unavailable", 0
    except Exception as e:
        print(f"元素翻译失败: {e}")
        return "error", 0

def translate_xml_file(file_path, progress_callback=None):
    """翻译XML文件中的指定标签内容，正确理解翻译方向并处理混合内容"""
    parser = etree.XMLParser(recover=True)
    try:
        tree = etree.parse(file_path, parser)
        xml_root = tree.getroot()  # 重命名为xml_root避免与全局的Tkinter root混淆

        # 统计变量
        total_elements = 0
        local_count = 0
        api_count = 0
        api_unavailable_count = 0
        error_count = 0
        skip_count = 0
        match_sum = 0  # 用于计算平均匹配度
        
        # 创建要处理的元素和目标的列表
        translation_tasks = []
        
        # 1. 查找具有相同父元素的PARA和PARAC对
        for parent in xml_root.xpath("//*[child::PARA and child::PARAC]"):  # 将root改为xml_root
            paras = parent.xpath("./PARA")
            paracs = parent.xpath("./PARAC")
            
            # 确保数量一致
            min_count = min(len(paras), len(paracs))
            for i in range(min_count):
                # 注意：从PARA(英文)中获取原文，将翻译结果写入PARAC(中文)
                translation_tasks.append((paras[i], paracs[i]))
                total_elements += 1
        
        # 2. 处理特殊情况：TITLEC(需翻译成中文)和TITLE(英文)
        for parent in xml_root.xpath("//*[child::TITLE and child::TITLEC]"):  # 将root改为xml_root
            titles = parent.xpath("./TITLE")
            titlecs = parent.xpath("./TITLEC")
            
            min_count = min(len(titles), len(titlecs))
            for i in range(min_count):
                # 从TITLE获取英文，翻译后放入TITLEC
                translation_tasks.append((titles[i], titlecs[i]))
                total_elements += 1
        
        # 3. 处理独立的PARAC标签（没有找到配对的PARA）
        for parac in xml_root.xpath("//PARAC[not(../PARA)]"):  # 将root改为xml_root
            translation_tasks.append((parac, None))
            total_elements += 1
        
        # 4. 处理独立的TITLEC标签（没有找到配对的TITLE）
        for titlec in xml_root.xpath("//TITLEC[not(../TITLE)]"):  # 将root改为xml_root
            translation_tasks.append((titlec, None))
            total_elements += 1

        # 5. 处理PARA和PARAC中的子元素
        for parent in xml_root.xpath("//*[child::PARA and child::PARAC]"):
            paras = parent.xpath("./PARA")
            paracs = parent.xpath("./PARAC")

            min_count = min(len(paras), len(paracs))
            for i in range(min_count):
                para = paras[i]
                parac = paracs[i]

                # 如果PARA/PARAC本身没有文本但有子元素
                if (not para.text or len(para.text.strip()) <= 1) and len(list(para)) > 0:
                    para_children = list(para)
                    parac_children = list(parac)

                    # 如果子元素数量相同，尝试按顺序配对
                    if len(para_children) == len(parac_children):
                        for j in range(len(para_children)):
                            if para_children[j].text and len(para_children[j].text.strip()) > 1:
                                # 将子元素的文本内容作为翻译任务添加
                                translation_tasks.append((para_children[j], parac_children[j]))
                                total_elements += 1
        
        # 存储原始元素数量，将总元素数翻倍以包括尾部文本处理
        original_elements = total_elements
        tail_text_elements = total_elements  # 估计尾部文本元素的数量
        total_elements = total_elements * 1.2  # 包括主文本和尾部文本
        
        print(f"找到 {original_elements} 个需要翻译的主要元素，估计处理 {tail_text_elements} 个尾部文本")
        
        if original_elements == 0:
            print(f"没有可翻译内容: {file_path}")
            return 0, 0, 0, 0, 0, 0
        
        # 重置性能统计
        global perf_stats
        perf_stats = {
            "total_time": 0,
            "match_count": 0,
            "elements_per_second": 0
        }
        
        # 初始化尾部文本处理计数器
        tail_text_processed = 0
        
        # 使用线程池实现高并发
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            # 为每个任务创建Future
            futures = []
            for source_elem, target_elem in translation_tasks:
                future = executor.submit(translate_element, source_elem, target_elem)
                futures.append(future)
            
            # 处理完成的任务
            for i, future in enumerate(concurrent.futures.as_completed(futures)):
                status, match_ratio = future.result()
                
                if status == "local":
                    local_count += 1
                    match_sum += match_ratio
                elif status == "api":
                    api_count += 1
                elif status == "api_unavailable":
                    api_unavailable_count += 1
                elif status == "error":
                    error_count += 1
                elif status == "skip":
                    skip_count += 1
                
                if progress_callback:
                    progress_callback(i + 1, total_elements)
        
        # 添加进度更新和状态提示
        print("主要文本翻译完成，开始处理嵌套标签后的尾部文本...")
        if progress_callback:
            progress_callback(original_elements, total_elements)
        
        # 使用全局的Tkinter窗口对象
        if 'status_label' in globals() and 'root' in globals():
            globals()['root'].after(0, lambda: status_label.config(text="正在收集标签尾部文本..."))

        # 第1步：收集所有需要处理的尾部文本
        tail_text_tasks = []

        # 找出所有PARAC和对应的PARA标签中的尾部文本
        for parent in xml_root.xpath("//*[child::PARA and child::PARAC]"):
            paras = parent.xpath("./PARA")
            paracs = parent.xpath("./PARAC")
            
            # 确保数量一致
            min_count = min(len(paras), len(paracs))
            for i in range(min_count):
                para = paras[i]
                parac = paracs[i]
                
                # 处理每个PARA中的子元素尾部文本
                para_children = list(para)
                parac_children = list(parac)
                
                # 处理子元素数量相同的情况
                if len(para_children) == len(parac_children):
                    for j in range(len(para_children)):
                        if para_children[j].tail and len(para_children[j].tail.strip()) > 1:
                            # 收集任务：源元素, 目标元素, 源文本
                            tail_text_tasks.append((para_children[j], parac_children[j], para_children[j].tail.strip()))
                # 处理子元素数量不同的情况
                else:
                    # 找出所有带尾部文本的子元素
                    for para_child in para_children:
                        if para_child.tail and len(para_child.tail.strip()) > 5:
                            eng_tail = para_child.tail.strip()
                            
                            # 尝试通过标签名匹配PARAC中的对应子元素
                            matching_children = [child for child in parac_children if child.tag == para_child.tag]
                            if matching_children:
                                # 添加到任务列表
                                tail_text_tasks.append((para_child, matching_children[0], eng_tail))

        print(f"收集到 {len(tail_text_tasks)} 个尾部文本需要处理")

        if not tail_text_tasks:
            print("没有尾部文本需要处理")
            # 保存结果
            tree.write(file_path, encoding='UTF-8', xml_declaration=True, pretty_print=True)
            # 返回统计信息
            avg_match = match_sum / local_count if local_count > 0 else 0
            return local_count, api_count, skip_count, error_count, avg_match, api_unavailable_count

        # 使用全局的Tkinter窗口对象
        if 'status_label' in globals() and 'root' in globals():
            globals()['root'].after(0, lambda: status_label.config(text=f"正在处理 {len(tail_text_tasks)} 个标签尾部文本..."))

        # 第2步：定义尾部文本处理函数
        def process_tail_text(task):
            src_elem, tgt_elem, eng_text = task
            
            # 尝试翻译
            start_time = time.time()
            local_translation, match_ratio = find_in_local_library(eng_text)
            elapsed = time.time() - start_time
            
            # 更新性能统计（通过结果返回而不是直接更新全局变量，避免线程安全问题）
            result = {
                "src_elem": src_elem, 
                "tgt_elem": tgt_elem, 
                "eng_text": eng_text,
                "elapsed": elapsed
            }
            
            if local_translation and match_ratio >= min_match_threshold:
                result["translation"] = local_translation
                result["match_ratio"] = match_ratio
                result["status"] = "local"
            elif client is not None:
                # 使用API翻译
                try:
                    result["translation"] = translate_text(eng_text)
                    result["match_ratio"] = 0
                    result["status"] = "api"
                except Exception as e:
                    result["status"] = "api_unavailable"
                    result["error"] = str(e)
            else:
                result["status"] = "api_unavailable"
            
            return result

        # 第3步：并行处理所有尾部文本
        # 获取配置的线程数
        threads = threads_var.get() if 'threads_var' in globals() else 4

        # 使用线程池并行处理
        with concurrent.futures.ThreadPoolExecutor(max_workers=threads) as executor:
            # 提交所有任务
            futures = [executor.submit(process_tail_text, task) for task in tail_text_tasks]
            
            # 处理完成的任务
            for i, future in enumerate(concurrent.futures.as_completed(futures)):
                try:
                    result = future.result()
                    status = result["status"]
                    
                    # 应用翻译结果
                    if status == "local" or status == "api":
                        result["tgt_elem"].tail = result["translation"]
                        
                    # 更新统计信息
                    if status == "local":
                        local_count += 1
                        match_sum += result["match_ratio"]
                    elif status == "api":
                        api_count += 1
                    elif status == "api_unavailable":
                        api_unavailable_count += 1
                    
                    # 更新性能统计
                    perf_stats["total_time"] += result.get("elapsed", 0)
                    perf_stats["match_count"] += 1
                    perf_stats["elements_per_second"] = perf_stats["match_count"] / perf_stats["total_time"] if perf_stats["total_time"] > 0 else 0
                    
                    # 更新进度
                    if progress_callback:
                        current_progress = original_elements + i + 1
                        progress_callback(current_progress, total_elements)
                except Exception as e:
                    print(f"处理尾部文本任务时出错: {e}")
                    error_count += 1

        # 添加文件保存前的状态更新
        print("尾部文本处理完成，正在保存文件...")
        if progress_callback:
            progress_callback(total_elements-1, total_elements)
        
        # 使用全局的Tkinter窗口对象
        if 'status_label' in globals() and 'root' in globals():
            globals()['root'].after(0, lambda: status_label.config(text="正在保存文件..."))
        
        # 计算平均匹配度
        avg_match = match_sum / local_count if local_count > 0 else 0
        
        # 保存结果
        tree.write(file_path, encoding='UTF-8', xml_declaration=True, pretty_print=True)
        
        print(f"翻译完成: {file_path}")
        print(f"统计: 本地匹配 {local_count} (平均匹配度: {avg_match:.1f}%), API调用 {api_count}, API不可用 {api_unavailable_count}, 跳过 {skip_count}, 错误 {error_count}")
        print(f"性能: 平均每秒处理 {perf_stats['elements_per_second']:.2f} 个元素")
        
        return local_count, api_count, skip_count, error_count, avg_match, api_unavailable_count
    except Exception as e:
        print(f"文件处理失败: {file_path} - {e}")
        import traceback
        traceback.print_exc()
        return 0, 0, 0, 0, 0, 0

def find_files_with_keyword(directory, keyword):
    """在指定目录中查找包含关键词的XML文件"""
    files_with_keyword = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.xml') and keyword in file:
                files_with_keyword.append(os.path.join(root, file))
    return files_with_keyword

def start_translation():
    """开始搜索文件"""
    keyword = keyword_entry.get()
    if not keyword:
        messagebox.showwarning("输入错误", "请输入关键词以搜索XML文件。")
        return

    global directory
    files_with_keyword = find_files_with_keyword(directory, keyword)
    if not files_with_keyword:
        messagebox.showinfo("未找到文件", f"在 {directory} 中未找到包含关键词 '{keyword}' 的XML文件")
        return

    file_listbox.delete(0, END)
    for file in files_with_keyword:
        file_listbox.insert(END, file)
    print(f"找到 {len(files_with_keyword)} 个包含关键词 '{keyword}' 的文件")

def update_progress(current, total):
    """更新进度条"""
    # 使用tkinter的after方法确保在主线程中更新UI
    root.after(0, lambda: progress_label.config(text=f"进度: {current}/{total}"))
    root.after(0, lambda: progress_bar.configure(value=(current / total) * 100))
    
    # 如果有性能统计，显示速度
    if perf_stats["elements_per_second"] > 0:
        root.after(0, lambda: speed_label.config(text=f"速度: {perf_stats['elements_per_second']:.2f} 元素/秒"))

def on_translate():
    """开始翻译选中的文件"""
    selected_files = [file_listbox.get(idx) for idx in file_listbox.curselection()]
    if not selected_files:
        messagebox.showwarning("未选择文件", "请选择一个或多个XML文件进行翻译。")
        return
        
    # 确保API已初始化
    global client
    api_initialized = False
    
    if client is None:
        api_key = api_key_var.get()
        api_initialized = initialize_client(api_key)
        # 如果API初始化失败，不显示错误消息，因为initialize_client已经显示了错误

    # 确保翻译库已加载
    if not translation_cache:
        count = load_translation_library(update_progress)
        status_label.config(text=f"已加载翻译库: {count}个条目")

    # 获取当前匹配阈值
    global min_match_threshold
    min_match_threshold = match_threshold_var.get()
    
    # 更新匹配器的阈值
    if translation_matcher:
        translation_matcher.update_threshold(min_match_threshold)

    def translate_files():
        total_local = 0
        total_api = 0
        total_skip = 0
        total_error = 0
        total_api_unavailable = 0  # 新增：总API不可用计数
        total_match_sum = 0
        
        # 不再显示API状态提示，因为界面上已经显示了
        
        for file in selected_files:
            local, api, skip, error, avg_match, api_unavailable = translate_xml_file(file, progress_callback=update_progress)
            total_local += local
            total_api += api
            total_skip += skip
            total_error += error
            total_api_unavailable += api_unavailable
            total_match_sum += local * avg_match if local > 0 else 0
        
        avg_total_match = total_match_sum / total_local if total_local > 0 else 0
        
        # 构建完成消息，包含API不可用信息
        completion_msg = f"所有指定文本已翻译并保存。\n\n" \
                         f"本地匹配: {total_local} (平均匹配度: {avg_total_match:.1f}%)\n" \
                         f"API调用: {total_api}\n"
        
        if total_api_unavailable > 0:
            completion_msg += f"API不可用/失败: {total_api_unavailable} (已保留原值)\n"
        
        completion_msg += f"跳过: {total_skip}\n" \
                          f"错误: {total_error}\n\n" \
                          f"设定的最低匹配阈值: {min_match_threshold}%\n" \
                          f"平均速度: {perf_stats['elements_per_second']:.2f} 元素/秒"
        
        root.after(0, lambda: messagebox.showinfo("翻译完成", completion_msg))

    print(f"开始翻译 {len(selected_files)} 个文件，最低匹配阈值: {min_match_threshold}%")
    translation_thread = threading.Thread(target=translate_files)
    translation_thread.start()

def update_threshold_label(value):
    """更新滑块标签显示"""
    threshold_value_label.config(text=f"{value}%")
    
    # 如果匹配器已经创建，同步更新其阈值
    global min_match_threshold, translation_matcher
    min_match_threshold = int(value)
    if translation_matcher:
        translation_matcher.update_threshold(min_match_threshold)

def choose_directory():
    """选择工作目录"""
    global directory
    selected_dir = filedialog.askdirectory(initialdir=directory)
    if selected_dir:
        directory = selected_dir
        directory_label.config(text=f"当前工作目录: {directory}")

def choose_library_directory():
    global xml_library_dir
    selected_dir = filedialog.askdirectory(initialdir=xml_library_dir)
    if selected_dir:
        xml_library_dir = selected_dir
        library_label.config(text=f"翻译库目录: {xml_library_dir}")
        # 保存配置
        save_config()
        # 提示用户是否要清除缓存并重新加载翻译库
        if messagebox.askyesno("重新加载", "是否要清除缓存并重新加载翻译库？"):
            clear_cache_and_rebuild_index()
        else:
            # 只重新加载翻译库，不清除缓存
            status_label.config(text="正在加载翻译库...")
            def load_lib_thread():
                count = load_translation_library(update_progress)
                root.after(0, lambda: status_label.config(text=f"已加载翻译库: {count}个条目"))
            threading.Thread(target=load_lib_thread).start()

def load_library():
    # 询问用户是否要清除缓存
    if messagebox.askyesno("重新加载", "是否要清除缓存并重新加载翻译库？"):
        clear_cache_and_rebuild_index()
    else:
        # 只重新加载翻译库，不清除缓存
        status_label.config(text="正在加载翻译库...")
        progress_bar['value'] = 0
        def load_lib_thread():
            count = load_translation_library(update_progress)
            root.after(0, lambda: status_label.config(text=f"已加载翻译库: {count}个条目"))
            root.after(0, lambda: progress_bar.configure(value=100))
        threading.Thread(target=load_lib_thread).start()

def save_api_settings():
    api_key = api_key_var.get()
    if not api_key:
        messagebox.showwarning("输入错误", "请输入有效的API Key。")
        return
    
    # 使用单一参数调用初始化函数
    if initialize_client(api_key):
        messagebox.showinfo("设置保存", "API设置已保存并初始化成功。")
        save_config()
        api_settings_frame.pack_forget()
    else:
        messagebox.showinfo("设置已保存", "API设置已保存，但API验证失败。\n将仅使用本地翻译库进行翻译。")
        save_config()
        api_settings_frame.pack_forget()

def show_api_settings():
    """显示API设置对话框"""
    api_settings_frame.pack(fill="x", padx=10, pady=10, after=frame_dirs)

def create_index():
    """手动创建或重建翻译索引"""
    global translation_matcher
    
    if not translation_cache:
        messagebox.showwarning("未加载翻译库", "请先加载翻译库。")
        return
    
    status_label.config(text="正在创建翻译索引...")
    progress_bar['value'] = 0
    
    def build_index_thread():
        global translation_matcher  # 添加全局声明以修复作用域问题
        
        if translation_matcher is None:
            translation_matcher = TranslationMatcher(translation_cache, min_match_threshold)
        
        start_time = time.time()
        translation_matcher.create_index(update_progress)
        elapsed = time.time() - start_time
        
        root.after(0, lambda: status_label.config(text=f"索引创建完成: {len(translation_cache)}个条目，耗时 {elapsed:.1f} 秒"))
        root.after(0, lambda: progress_bar.configure(value=100))
    
    threading.Thread(target=build_index_thread).start()

# 创建主窗口
root = tk.Tk()
root.title("XML 翻译工具 - 马士航")
root.geometry("800x800")  # 设置更合适的初始窗口大小

def set_app_icon():
    icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "xml-translator-icon.png")
    
    if os.path.exists(icon_path):
        # 使用PhotoImage加载图标
        icon = tk.PhotoImage(file=icon_path)
        # 设置应用程序图标（适用于dock/任务栏）
        root.iconphoto(True, icon)
        
        # 对于Windows，还可以设置任务栏图标
        if os.name == 'nt':  # Windows系统
            import ctypes
            myappid = 'company.product.xmltranslator.1.0'  # 任意字符串，但应保持唯一
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)
    else:
        print(f"警告: 找不到图标文件 {icon_path}")

# 调用设置图标函数
set_app_icon()
        
# 创建顶部框架容器
frame_top = tk.Frame(root)
frame_top.pack(fill="x", padx=10, pady=5)

# 创建搜索控件
Label(frame_top, text="输入关键词以搜索XML文件:").pack(side="left", padx=5)
keyword_entry = Entry(frame_top, width=30)
keyword_entry.pack(side="left", padx=5)
Button(frame_top, text="搜索", command=start_translation).pack(side="left", padx=5)

# API状态标签
api_status_label = Label(frame_top, text="API状态: 未配置")
api_status_label.pack(side="right", padx=5)

# 文件列表框架
frame_list = tk.Frame(root)
frame_list.pack(fill="both", expand=True, padx=10, pady=5)

file_listbox = Listbox(frame_list, selectmode=SINGLE, width=100, height=15)
file_listbox.pack(side="left", fill="both", expand=True)

scrollbar = Scrollbar(frame_list, orient="vertical")
scrollbar.config(command=file_listbox.yview)
scrollbar.pack(side="right", fill="y")

file_listbox.config(yscrollcommand=scrollbar.set)

# 匹配阈值设置框架
frame_threshold = tk.Frame(root)
frame_threshold.pack(fill="x", padx=10, pady=5)

Label(frame_threshold, text="匹配阈值:").pack(side="left", padx=5)
match_threshold_var = IntVar(value=min_match_threshold)
threshold_slider = Scale(frame_threshold, from_=85, to=100, orient="horizontal", 
                         variable=match_threshold_var, length=300,
                         command=update_threshold_label)
threshold_slider.pack(side="left", padx=5)
threshold_value_label = Label(frame_threshold, text=f"{min_match_threshold}%")
threshold_value_label.pack(side="left", padx=5)

# 操作按钮框架
frame_buttons = tk.Frame(root)
frame_buttons.pack(fill="x", padx=10, pady=5)

Button(frame_buttons, text="翻译选中文件", command=on_translate, 
       bg="#4CAF50", fg="white", width=15, height=2).pack(side="left", padx=5)
Button(frame_buttons, text="加载翻译库", command=load_library, 
       width=15, height=2).pack(side="left", padx=5)
Button(frame_buttons, text="创建索引", command=create_index, 
       width=15, height=2).pack(side="left", padx=5)
Button(frame_buttons, text="API设置", command=show_api_settings, 
       width=15, height=2).pack(side="left", padx=5)

# 进度框架
frame_progress = tk.Frame(root)
frame_progress.pack(fill="x", padx=10, pady=5)

progress_label = Label(frame_progress, text="进度: 0/0")
progress_label.pack(side="top", pady=2)

progress_bar = ttk.Progressbar(frame_progress, length=400)
progress_bar.pack(side="top", pady=2, fill="x")

speed_label = Label(frame_progress, text="速度: 0.00 元素/秒")
speed_label.pack(side="top", pady=2)

status_label = Label(frame_progress, text="翻译库未加载")
status_label.pack(side="top", pady=2)

# 目录框架
frame_dirs = tk.Frame(root)
frame_dirs.pack(fill="x", padx=10, pady=5)

directory_label = Label(frame_dirs, text=f"翻译文件位置: {directory}")
directory_label.pack(side="top", anchor="w", pady=2)
Button(frame_dirs, text="选择翻译文件位置", command=choose_directory).pack(side="top", anchor="w", pady=2)

library_label = Label(frame_dirs, text=f"翻译库目录: {xml_library_dir}")
library_label.pack(side="top", anchor="w", pady=2)
Button(frame_dirs, text="选择翻译库目录", command=choose_library_directory).pack(side="top", anchor="w", pady=2)

# API设置框架 (初始不显示)
api_settings_frame = tk.Frame(root, relief="ridge", borderwidth=2, padx=10, pady=10, bg="#f0f0f0")

Label(api_settings_frame, text="API设置", font=("Arial", 12, "bold"), bg="#f0f0f0").pack(anchor="w", pady=5)
# API设置框架 (初始不显示)
api_settings_frame = tk.Frame(root, relief="ridge", borderwidth=2, padx=10, pady=10, bg="#f0f0f0")

Label(api_settings_frame, text="智谱AI设置", font=("Arial", 12, "bold"), bg="#f0f0f0").pack(anchor="w", pady=5)

# API Key设置
api_key_frame = Frame(api_settings_frame, bg="#f0f0f0")
api_key_frame.pack(fill="x", pady=5)
Label(api_key_frame, text="API Key:", width=10, anchor="w", bg="#f0f0f0").pack(side="left", padx=5)
api_key_var = StringVar(value=DEFAULT_API_KEY)
api_key_entry = Entry(api_key_frame, textvariable=api_key_var, width=60, show="*")
api_key_entry.pack(side="left", fill="x", expand=True, padx=5)

# API设置操作按钮
api_buttons_frame = Frame(api_settings_frame, bg="#f0f0f0")
api_buttons_frame.pack(fill="x", pady=10)
Button(api_buttons_frame, text="保存并应用", command=save_api_settings, 
       bg="#4285F4", fg="white", width=15).pack(side="left", padx=5)
Button(api_buttons_frame, text="取消", command=lambda: api_settings_frame.pack_forget(), 
       width=10).pack(side="left", padx=5)

# 性能设置框架
perf_frame = tk.Frame(root)
perf_frame.pack(fill="x", padx=10, pady=5)

Label(perf_frame, text="性能调优", font=("Arial", 10, "bold")).pack(side="top", anchor="w", pady=2)

threads_frame = Frame(perf_frame)
threads_frame.pack(fill="x", anchor="w", pady=2)
Label(threads_frame, text="线程数:").pack(side="left", padx=5)
threads_var = IntVar(value=8)
threads_scale = Scale(threads_frame, from_=1, to=8, orient="horizontal", variable=threads_var, length=200)
threads_scale.pack(side="left", padx=5)

# 帮助信息
help_text = """使用说明:
1. 加载翻译库：程序启动后自动从缓存加载，如选择其他目录或增加文件，可再次点击加载
2. 创建索引：如程序加载索引失败，可点击此处再次尝试
3. 搜索XML文件：输入关键词找到需要翻译的文件
4. 设置匹配阈值：调整滑块设置模糊匹配的最低接受程度(85%-100%)"""

help_label = Label(root, text=help_text, justify="left", bg="#f0f0f0", padx=10, pady=10)
help_label.pack(fill="x", padx=10, pady=10)

# 初始加载翻译库
def delayed_load():
    # 首先加载配置
    load_config()
    # 更新UI以反映加载的配置
    if 'api_key_var' in globals():
        api_key_var.set(DEFAULT_API_KEY)
    # ...
    
    # 然后加载翻译库
    status_label.config(text="正在加载翻译库...")
    def load_thread():
        count = load_translation_library(update_progress)
        root.after(0, lambda: status_label.config(text=f"已加载翻译库: {count}个条目"))
        
        # 使用与save_api_settings相同的方法初始化API
        api_key = DEFAULT_API_KEY.strip()  # 确保没有空格
        if initialize_client(api_key):
            root.after(0, lambda: api_status_label.config(text="API状态: 已配置 (智谱AI)"))
        else:
            # 不显示错误信息，因为这是初始启动
            root.after(0, lambda: api_status_label.config(text="API状态: 未配置 (请在设置中配置)"))
    
    threading.Thread(target=load_thread).start()

def on_closing():
    save_config()
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_closing)

root.after(1000, delayed_load)  # 延迟1秒加载，确保UI已经完全加载

# 运行主循环
root.mainloop()
