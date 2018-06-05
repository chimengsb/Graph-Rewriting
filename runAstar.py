import os, hashlib, json, itertools, sys, time
from random import randint
import queue as Q

'''
Basic Graph 中存储的格式示例

graph = {
    'Alice': {
        'type': 'Girl',
        'edges': [{
            'name': 'is_wife_of',
            'to': 'Bob'
        }, {
            'name': 'is_sister_of',
            'to': 'Carol'
        }]
    },
    'Bob': {
        'type': 'Boy',
        'edges':[]
    },
    'Carol':{
        'type': 'Girl',
        'edges': [{
            'name': 'is_mother',
            'to': 'Bob'
        }]
    }
}
'''
class Basic_Graph:
    # 存储图结构，包含一个字典self.graph，其中存储了顶点和边的信息，格式可以参照上面的注释内容
    # graph, rules, goal 都从这个类衍生
    def __init__(self, objects, relations):
        self.graph = {}
        # 按照json文件中的格式，添加边和顶点
        for item in objects:
            # 添加顶点
            name = item['id']
            type_ = item['type']
            if name not in self.graph:
                # 每个顶点包含了 type 信息，和它的出边：一个edges数组
                self.graph[name] = {'type': type_, 'edges': []}

        for relation in relations:
            # 添加边
            source = relation['source']
            target = relation['target']
            name = relation['type']
            # edges 中的每一条边 edge 都包含了他的名字 和 另一个断点的名字的信息
            self.graph[source]['edges'].append({'name': name, 'to': target})
    
    def __str__(self):
        # 用于最后打印结果
        string = ''
        for v, info in self.graph.items():
            string += ('%s of Type %s \n'%(v, info['type']))
            for edge in info['edges']:
                string += ('    --> %s --> %s \n'%(edge['name'], edge['to']))
            string += ('\n')
        return string

class Goal:
    # Goal 对象，包含了goal中的信息：一个graph 和 nacs
    def __init__(self, goal):
        self.nacs = [Basic_Graph(nac['objects'], nac.get('relations', [])) for nac in goal.get('nacs', [])]
        if goal['graph'] != {}:
            self.graph = Basic_Graph(goal['graph']['objects'], goal['graph'].get('relations', []))
        else :
            self.graph = {}

class Rule:
    # Rule 对象，包含了id，lhs，rhs，nacs等部分
    # lhs, rhs, nac 都是Basic_Graph对象
    def __init__(self, rule):
        self.id = rule['id']
        # 因为relations是可选的，所以不一定有relations，如果没有就用空的list[]
        self.lhs = Basic_Graph(rule['lhs']['objects'], rule['lhs'].get('relations', []))
        self.rhs = Basic_Graph(rule['rhs']['objects'], rule['rhs'].get('relations', []))
        self.nacs = [Basic_Graph(nac.get('objects', []), nac.get('relations', [])) for nac in rule.get('nacs', [])]

class Main_Graph(Basic_Graph):
    # 待解决的问题，包含了这个问题的graph, goal, rules等属性和一系列图变换的方法
    def __init__(self, objects, relations, goal, rules):
        Basic_Graph.__init__(self, objects, relations)
        self.goal = goal    # goal 是一个 Goal 对象
        self.rules = rules  # rules 是 Rule 对象的一个list
        self.visited = set()# 一个集合，记录了已经到达过的状态，避免重复搜索
        self.comp_time = 0  # 记录比较次数

    def match_goal(self, goal):
        # 如果任意一个 nac 被匹配，就没有成功
        for nac in goal.nacs:
            match_nac = self.match_graph(self.graph, nac.graph)
            if match_nac :
                return False, len(match_nac)
        # 如果 goal.graph 为空，说明已经达成了goal
        if not goal.graph:
            return True, 0
        # 否则需要检查是否满足graph
        return bool(self.match_graph(self.graph, goal.graph)), 0

    def match_rule(self, rule):
        matches = self.match_graph(self.graph, rule.lhs.graph)
        # 先与lhs匹配，找到所有可能的匹配，接下来匹配nacs
        # 把所有不满足nacs的可能匹配给保留
        good_matches = []
        for match in matches:
            flag = False
            for nac in rule.nacs:
                if self.match_nac(match, nac, rule.lhs):
                    flag = True
                    break
            if flag is False:
                good_matches.append(match)
        return good_matches

    def apply_rule(self, rule, match):
        # 参数
        # rule: 将要apply 的rule
        # match: 是一组满足条件的点之间的映射，即从原图 到 lhs 的一个点映射
        mapping = {}
        for pair in match:
            mapping[pair[1]] = pair[0]

        for v, info in rule.rhs.graph.items():
            # lhs中没有，但是rhs中有的点，要在原图中新增
            if v not in rule.lhs.graph.keys():
                # 生成新的点，并给他取一个不容易重复的名字
                new_name = str(randint(0, 10000)) + v + str(randint(0, 10000))
                self.graph[new_name] = {'type': info['type'], 'edges': []}
                match.append((new_name, v))
                # 不同时把边也加上去是因为边的某个顶点可能此时还没加进原图，直接加边会出错

        for v, info in rule.lhs.graph.items():
            # 查找 lhs 中有，但是 rhs 中没有的元素（点和边）
            if v not in rule.rhs.graph.keys():
                # 如果 lhs 中有顶点，但是 rhs中没有顶点
                name = mapping[v]
                # 删除该节点
                self.graph.pop(name)
                continue

            delete_edges = []
            # 寻找要被删掉的边
            for edge in info['edges']:
                flag = False
                for r_edge in rule.rhs.graph[v]['edges']:
                    if r_edge == edge:
                        flag = True
                        break
                # 在lhs中的边 如果在rhs中没找到
                if flag is False:
                    from_name = mapping[v]
                    to_name =  mapping[edge['to']]
                    delete_edge = {'name': edge['name'], 'to': to_name}
                    # 删掉在原图中相对应的边
                    self.graph[from_name]['edges'].remove(delete_edge)

        for v, info in rule.rhs.graph.items():
            # 增加边
            if v not in rule.lhs.graph.keys():
                # 如果有一些点是之前新加的，把它的出边全部加上
                for edge in info['edges']:
                    from_v = mapping[v]
                    to_v = mapping[edge['to']]
                    new_edge = {'name': edge['name'], 'to': to_v}
                    self.graph[from_v]['edges'].append(new_edge)
                continue

            for edge in info['edges']:
                # 查找要增加的边
                flag = False
                for r_edge in rule.lhs.graph[v]['edges']:
                    if r_edge == edge:
                        flag = True
                        break
                # 在lhs中的边 如果在rhs中没找到
                if flag is False:
                    from_v = mapping[v]
                    to_v = mapping[edge['to']]
                    new_edge = {'name': edge['name'], 'to': to_v}
                    # 在原图中添加相对应的边
                    self.graph[from_v]['edges'].append(new_edge)

    def match_nac(self, match, nac, lhs):
        # 匹配 nac，考虑到lhs和nac中名字相同的点必须是相同的，这里把这一部分点先挑出来
        # 求交集
        pv_in_both_nac_lhs = set(nac.graph.keys()).intersection(lhs.graph.keys())
        intersect_tuples = {(pair[0], pair[1]) for pair in match if pair[1] in pv_in_both_nac_lhs}
        res = self.match_graph(self.graph, nac.graph, intersect_tuples)
        return bool(res)

    def match_graph(self, graph, pattern_graph, must_match_pairs = set()):
        # 匹配同构子图
        # 参数：
        # graph: 待匹配的图
        # pattern_graph: 匹配的模板图，即要从graph中，找到所有与pattern_graph同构的子图
        # must_match_pairs: 用于nac的查找，如果nac与lhs中有相同的元素，那么在匹配nac时，
        #                   这些元素必须参与匹配，缺省时为空集
        def check_violate(possible_match, vs, pvs):
            # 参数：
            # possible_match: 一个可能匹配的完整的映射，需要检验它们是否存在冲突
            # vs, pvs: 原图和模板图的顶点集合
            # 方法：

            # mapping 是从模板顶点 到 原图的顶点的映射
            mapping = {}
            for pair in possible_match:
                mapping[pair[1]] = pair[0]
            # 检查模板中的每一条边在原图中是否存在
            for pv, pinfo in pattern_graph.items():
                for edge in pinfo['edges']:
                    mapping_edge = {'name': edge['name'], 'to': mapping[edge['to']]}
                    if mapping_edge not in graph[mapping[pv]]['edges']:
                        return True
            # 未发现冲突
            return False
            
        # waiting_list: 经过初步筛选之后的可能的点映射的集合
        waiting_list = set()
        for pattern_v, pattern_info in pattern_graph.items():
            for v, info in graph.items():
                # 可能的映射: 
                # 必要条件1: 类型相同 and 必要条件2: 原图的出度>= pattern中的出度 
                if info['type'] == pattern_info['type'] and len(info['edges']) >= len(pattern_info['edges']):
                    # 必要条件3: pattern中每一个relation的名字都必须被包含
                    relation_names = [ e['name'] for e in info['edges']]
                    flag = True
                    for edge in pattern_info['edges']:
                        if edge['name'] in relation_names:
                            relation_names.remove(edge['name'] )
                        else:
                            flag = False
                            break
                    # v --> pattern_v 是一个可能的映射
                    if flag is True:
                        waiting_list.add((v,pattern_v))
        
        r = len(pattern_graph) # 模板的点的数目

        if must_match_pairs:
            # 如果有必须参加匹配的点对，那么就从waiting_list里面把与它们名字相同的都去掉。因为是双射。
            new_waiting_list = set()
            for pair in must_match_pairs:
                for waiting_pair in waiting_list:
                    if waiting_pair[0] != pair[0] and waiting_pair[1] != pair[1]:
                        new_waiting_list.add(waiting_pair)
                new_waiting_list.add(pair)
            waiting_list = new_waiting_list

        # matches 中的 每一个 match 都是一组成功的匹配
        matches = []
        # 从waiting_list中，选取所有可能的 r 个顶点的 组合，进行验证，验证它们之间所有的边的关系是否不冲突
        for possible_match in itertools.combinations(waiting_list, r):
            vs, pvs = map(list, zip(*possible_match))
            if len(set(vs)) < len(vs) or len(set(pvs)) < len(pvs):
                # 不能有重复的点, 因为必须是一一对应的
                continue
            if not check_violate(possible_match, vs, pvs):
                matches.append(possible_match)

        return matches


    # 递归会爆栈 用循环
    def dfs(self):
        stack = [self.graph]
        while stack:
            prev_graph = stack.pop()
            # 判断是否之前遍历过这个状态
            prev_hash = self.hash_(prev_graph) 
            if prev_hash not in self.visited:
                self.visited.add(prev_hash)
                self.graph = self.deepcopy_dict(prev_graph)
                # 应用rules，得到遍历的子节点，将其入栈
                for rule in self.rules:
                    matches = self.match_rule(rule)
                    for match in matches:
                        self.apply_rule(rule, match)
                        self.comp_time += 1
                        if self.match_goal(self.goal)[0]:
                            return True
                        stack.append(self.graph)
                        self.graph = self.deepcopy_dict(prev_graph)
        return False
 
    def bfs(self):
        que = Q.PriorityQueue()
        success, nac_cnt = self.match_goal(self.goal)
        if success:
            return True

        que.put(PriorityEntry(-nac_cnt, 0, self.graph))

        while not que.empty():
            prev = que.get()
            prev_graph = prev.graph
            self.comp_time += 1
            roadsum = prev.roadsum + 1
            self.graph = self.deepcopy_dict(prev_graph)
            # 应用rules，得到遍历的子节点，判断在之前有没有遍历，如果没有将其入队列
            #roadsum指的是从begin state到current state需要的最少操作次数，由于所有结点加入队列时必定是第一次出现，因此将其可以将其父节点roadsum + 1表示此节点的roadsum
            for rule in self.rules:
                matches = self.match_rule(rule)
                for match in matches:
                    self.apply_rule(rule, match)
                    success, nac_cnt = self.match_goal(self.goal)
                    if success:
                        return True
                    else :
                        # 判断是否之前遍历过这个状态
                        son_hash = self.hash_(self.graph)
                        if son_hash not in self.visited:
                            self.visited.add(son_hash)
                            que.put(PriorityEntry(-nac_cnt, roadsum , self.graph))
                    self.graph = self.deepcopy_dict(prev_graph)
        return False

    ############################ 以下是一些辅助函数
    def hash_(self, a):
        # get a unique id for a dictionary
        return(hashlib.sha1(json.dumps(a, sort_keys=True).encode('utf-8')).hexdigest())
    def get_subgraph(self, graph, vs):
        # 求 graph 限制在 vs 顶点集中的子图
        subgraph = {}
        for v, info in graph.items():
            if v in vs:
                subgraph[v] = {'type': info['type'], 'edges': []}
                for edge in info['edges']:
                    if edge['to'] in vs:
                        subgraph[v]['edges'].append(edge)
        return subgraph

    def deepcopy_dict(self, dic):
        # 深拷贝
        # python 自带的深拷贝函数太慢了，不如自己遍历一遍
        new_dict = {}
        for v, info in dic.items():
            edges = []
            for edge in info['edges']:
                edges.append({'name': edge['name'], 'to': edge['to']})
            new_dict[v] = {'type': info['type'], 'edges': edges}
        return new_dict

class PriorityEntry():

    def __init__(self, priority, roadsum , graph):
        self.graph = graph
        self.priority = priority
        self.roadsum = roadsum

    def __lt__(self, other):
        #利用A*算法估值排序
        return self.priority - self.roadsum < other.priority - other.roadsum

if __name__ == '__main__':
    dir_name = 'examples/Hanoi'
    with open(dir_name + '/goal.json') as f:
        goal_json = f.read()
    with open(dir_name + '/rules.json') as f:
        rules_json = f.read()
    with open(dir_name + '/instances/' + '7disks_3rods.json') as f:
        instance_json = f.read()

    # 读取 goal.json 文件
    goal = json.loads(goal_json)
    goal = Goal(goal)
    # 读取 rules.json 文件
    rules = json.loads(rules_json)
    rules = [Rule(rule) for rule in rules]
    # 读取 instance/trivial.json 文件
    graph = json.loads(instance_json)
    graph = Main_Graph(graph['objects'], graph.get('relations', []), goal, rules)
    start_time = time.time()

    if graph.bfs():
        print("--- %s seconds ---" % (time.time() - start_time))
        print('success\n')#final state:\n', graph)
    else:
        print("--- %s seconds ---" % (time.time() - start_time))
        print('fail')
    print(graph.comp_time)

