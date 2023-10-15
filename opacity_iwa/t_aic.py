# -*- coding:utf-8 -*-
import networkx as nx
import io
import yaml
import copy
from itertools import combinations, product
from heapq import heappush, heappop
from itertools import count
from collections import Counter

max_edge_number = 3

# A, B 形如 [[0,2],[5,10]...]
def intervalIntersection(A, B):     # https://blog.csdn.net/Desgard_Duan/article/details/100789337
    i, j = 0, 0
    res = []
    while i < len(A) and j < len(B):
        # ...
        j += 1
        i += 1
    return res

def get_event(iwa, start, end):
    return iwa.edge[start][end][0]['event']

def get_t_min(iwa, start, end):
    return iwa.edge[start][end][0]['t_min']

def get_t_max(iwa, start, end):
    return iwa.edge[start][end][0]['t_max']

def state_type(state):
    if type(state[0]) == tuple and list(state).__len__() == 2:      ## 先用2，后面要记得改成3，判断方式也要细改一下
        return 'Z_state'
    else:
        return 'Y_state'

def get_policy_event(state):
    policy_events = []
    for policy_t in state[1]:       ## 后面要改成state[2]
        policy_events.append(policy_t[0])
    return policy_events

def get_policy_t_min(state):
    policy = {}
    for policy_t in state[1]:       ## 后面要改成state[2]
        policy.update({policy_t[0] : policy_t[1]})
    return policy
def get_policy_duration(state):
    policy = {}
    for policy_t in state[1]:       ## 后面要改成state[2]
        policy.update({policy_t[0] : (policy_t[1], policy_t[2])})
    return policy

def get_min_max_time_from_y(iwa, y_state, current_node):
    t_min = 1e6  # 这也是个min-max结构，对每一个y状态求解y->z->y的最短路径
    t_max = -1
    G0 = nx.MultiDiGraph()
    for edge_g in iwa.edges():
        start = list(edge_g)[0]
        end = list(edge_g)[1]
        try:
            event =  iwa.edge[start][end][0]['event']
            t_min =  iwa.edge[start][end][0]['t_min']
            t_max = -iwa.edge[start][end][0]['t_max']  # 用负值，得到的最短距离就是最长距离
            G0.add_edge(start, end, event=event, t_min=t_min, t_max=t_max)
        except:
            pass

    for node_s in y_state:
        try:
            t_min_t = nx.shortest_path_length(G0, node_s, current_node, weight='t_min', method='bellman-ford')
            if t_min_t < t_min:
                t_min = t_min_t
            t_max_t = -nx.shortest_path_length(G0, node_s, current_node, weight='t_max', method='bellman-ford')     ## 现在是这个搞不定
            if t_max_t > t_max:
                t_max = t_max_t
        except:
            pass

    return [t_min, t_max]

def dfs_edges(G, event_list, event_uc, event_uo, source=None, depth_limit=None):
    if source is None:
        # edges for all components
        nodes = G
    else:
        # edges for components with source
        nodes = [source]
    visited = set()
    if depth_limit is None:
        depth_limit = len(G)
    for start in nodes:
        if start in visited:
            continue
        visited.add(start)
        stack = [(start, depth_limit, iter(G[start]))]
        while stack:
            parent, depth_now, children = stack[-1]
            try:
                child = next(children)

                if G.edge[parent][child][0]['event'] in event_list or \
                    (G.edge[parent][child][0]['event'] in event_uo and G.edge[parent][child][0]['event'] in event_uc):        # 加了这个, 而且加了后面一句, 对于所有uc都是直通的
                    if str([parent, child]) not in visited:     # 因为list本身不可哈希，所以用str(list())来代替list
                        yield parent, child                     # yield parent, child 这个版本的python没法调试yield  https://zhuanlan.zhihu.com/p/268605982
                        visited.add(str([parent, child]))       # visited.add(child)
                        if depth_now > 1:
                            stack.append((child, depth_now - 1, iter(G[child])))

            except StopIteration:
                stack.pop()

def dfs_ur(dfs_tree, sc, event_uc, event_uo, source=None, depth_limit=None):
    if source is None:
        # edges for all components
        nodes = dfs_tree
    else:
        # edges for components with source
        nodes = [source]
    visited = set()
    if depth_limit is None:
        depth_limit = len(dfs_tree)
    for start in nodes:
        if start in visited:
            continue
        visited.add(start)
        stack = [(start, depth_limit, iter(dfs_tree[start]))]
        while stack:
            parent, depth_now, children = stack[-1]
            try:
                child = next(children)

                is_edge_reachable = False         # added
                for sc_t in sc:
                    event_t = list(sc_t)[0]
                    event_c = dfs_tree.edge[parent][child][0]['event']
                    t = list(sc_t)[1]
                    if ((event_t == event_c and dfs_tree.edge[parent][child][0]['t_min'] <= t) or
                        (event_c in event_uc and event_c in event_uo)):
                        is_edge_reachable = True
                        break
                if not is_edge_reachable:
                    continue

                if str([parent, child]) not in visited:     # 因为list本身不可哈希，所以用str(list())来代替list
                    yield parent, child                     # yield parent, child 这个版本的python没法调试yield  https://zhuanlan.zhihu.com/p/268605982
                    visited.add(str([parent, child]))       # visited.add(child)
                    if depth_now > 1:
                        stack.append((child, depth_now - 1, iter(dfs_tree[child])))

            except StopIteration:
                stack.pop()

def dfs_events(iwa, event_list, event_uc, event_uo, source):
    edges = list(dfs_edges(iwa, event_list, event_uc, event_uo, source))

    G0 = nx.MultiDiGraph()

    for edge_t in edges:
        start = list(edge_t)[0]
        end   = list(edge_t)[1]
        try:
            event = iwa.edge[start][end][0]['event']
            if event in event_list or (event in event_uo and event in event_uc):                                 # 计算路径长的时候不能过可观事件
                t_min =  iwa.edge[start][end][0]['t_min']
                t_max = -iwa.edge[start][end][0]['t_max']          # 用负值，得到的最短距离就是最长距离
                G0.add_edge(start, end, event=event, t_min=t_min, t_max=t_max)
        except:
            pass

    # 这里用了个笨办法
    # 因为真正得到的dfs_tree的t_min和t_max要是累计值，而且累计值必须从取出的edge里面出
    # 所以这里先用取出的edge建了个图，然后在这个图里面做最短/最长路径
    dfs_tree = nx.MultiDiGraph()
    for edge_t in edges:
        start = list(edge_t)[0]
        end   = list(edge_t)[1]
        try:
            event = iwa.edge[start][end][0]['event']

            if event not in event_list:                                                                                                      # 这个是之前的版本遗留下来的，那个时候希望dfs_tree到一个可观事件然后停止，所以需要这么计算
                G0.add_edge(start, end, event=event, t_min=iwa.edge[start][end][0]['t_min'], t_max=-iwa.edge[start][end][0]['t_max'])      # 这个操作很暴力，因为如果要算过可观事件的min_max距离，那只有这条可观边是可走的，那么就在计算的时候加进来，算完就删掉
                #t_min =  nx.shortest_path_length(G0, source, end, weight='t_min')
                #t_max = -nx.shortest_path_length(G0, source, end, weight='t_max')
                t_min  = nx.shortest_path_length(G0, source, start, weight='t_min') + iwa.edge[start][end][0]['t_min']       # 避免计算结果为0，比如从6→6
                t_max = -nx.shortest_path_length(G0, source, start, weight='t_max') + iwa.edge[start][end][0]['t_max']       # 其实start→end是必经边，这个信息其实很关键
                G0.remove_edge(start, end)
            else:
                #t_min =  nx.shortest_path_length(G0, source, end, weight='t_min')
                #t_max = -nx.shortest_path_length(G0, source, end, weight='t_max')
                t_min  = nx.shortest_path_length(G0, source, start, weight='t_min') + iwa.edge[start][end][0]['t_min']
                t_max = -nx.shortest_path_length(G0, source, start, weight='t_max') + iwa.edge[start][end][0]['t_max']

            dfs_tree.add_edge(start, end, event=event, t_min=t_min, t_max=t_max)
        except:
            pass

    # 到这里计算到的都是通过uo到达的最短路径
    # 那些可经由可达时间到达的点还没有做出来
    for edge_t in edges:
        start = list(edge_t)[0]
        end   = list(edge_t)[1]

    return dfs_tree

def timeslice(dfs_tree):
    t_interval = []
    for edge_t in  dfs_tree.edges():
        t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_min']
        t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_max']
        t_interval.append(t_min)
        t_interval.append(t_max)

    t_interval = list(set(t_interval))      # 排序，去除多余元素
    t_interval.sort()
    return t_interval

def timeslice_events(dfs_tree, event_list):
    t_interval = []
    for edge_t in  dfs_tree.edges():
        if dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][list(edge_t)[2]]['event'] in event_list:
            t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_min']
            t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_max']
            t_interval.append(t_min)
            t_interval.append(t_max)

    t_interval = list(set(t_interval))
    t_interval.sort()
    return t_interval

def t_aic(iwa, source, event_uo, event_o, event_c, event_uc):
    # 把初始点设置为Y state
    bts = nx.MultiDiGraph()
    bts.add_node(tuple(source))
    bts_start = tuple(source)

    event_uo_c  = set(event_uo) & set(event_c)          # & 求交集
    event_uo_uc = set(event_uo) & set(event_uc)

    # 先求可控事件的全子集
    events_2c = []
    for index in range(list(event_c).__len__()):
        for subset_t in combinations(list(event_c), index + 1):
            events_2c.append(list(subset_t))
    events_2uo_uc = []
    for index in range(list(event_uo_uc).__len__()):
        for subset_t in combinations(list(event_uo_uc), index + 1):
            events_2uo_uc.append(list(subset_t))

    # 因为不可观不可控事件可以认为在supervisor中强制打开的，所以直接加入就好了，这里用笛卡尔积的形式直接算到了所有事件的组合形式
    supervisor_ut = []
    for _iter in product(list(events_2c), list(events_2uo_uc)):
        _iter = list(_iter)[0] + list(_iter)[1]
        supervisor_ut.append(_iter)


    ###################################################################################################################
    #
    # 这一部分应该才开始迭代

    # 核心思路：Z->Z的状态，可以通过dfs_tree全部求出
    #         所以我们只要求出下一时刻的Y状态
    #         同时，应注意，到达Y状态，supervisor清零，所以其实不用特别在意时间，只是求NX(·)的时候注意时间就好了
    # 思路：
    # 1 对Y state的每一个点求dfs_tree
    # 2
    # 结束条件：没有新的y_state可生成
    y_stack = []
    visited = []

    y_stack.append(tuple(bts_start))
    visited.append(tuple(bts_start))
    while y_stack:
        # 编程的时候你就想着，如果这个自动机有两个入口你怎么办
        current_state = y_stack.pop()

        for sc in supervisor_ut:
            t_interval = []

            max_time_uo = {}
            min_time_uo = {}
            sc_event_tuple = []
            for event_t in list(sc):
                max_time_uo.update({event_t: -1})
                min_time_uo.update({event_t: 1e6})
            for current_node in current_state:
                sc_uo = list(set(event_uo) & set(sc))
                dfs_tree = dfs_events(iwa, sc_uo, event_uc=event_uc, event_uo=event_uo, source=current_node)                    ## 待增加对环状结构的适应性
                t_interval = list(set(t_interval) | set(timeslice(dfs_tree)))
                t_interval.sort()


                # 求出不同事件对应的时间的最大值
                for u, v, data in dfs_tree.out_edges(data=True):                 # u, v, data in dfs_tree.out_edges(curr_node, data=True)
                    for event_t in list(sc):
                        if data['event'] in sc and data['t_max'] > max_time_uo[event_t]:
                            max_time_uo[data['event']] = data['t_max']
                        if data['event'] in sc and data['t_min'] < min_time_uo[event_t]:
                            min_time_uo[data['event']] = data['t_min']              # 用了个笨办法来处理可观可控事件，因为它不能往下走，所以对他的使能时间有个限制

            # 从timeslice内选取不超过时间最大值的时间，给对应事件
            for _iter in max_time_uo.keys():
                sc_timed_t = []

                '''
                if _iter not in event_c and _iter in event_uo:
                    t_interval_uc_uo = timeslice_events(dfs_tree, [_iter])      # 对不可观事件, 用它自己的一个timeslice, 反正到最后计算dfs_ur()的时候都是一起计算无所谓
                    for t in t_interval_uc_uo:
                        if _iter in event_uo and t < max_time_uo[_iter]:
                            sc_timed_t.append((_iter, t))
                else:
                '''
                if _iter in event_c and _iter in event_uo:
                    # 可控不可观事件
                    for t in t_interval:
                        if _iter not in event_uo and t >= min_time_uo[_iter] and t < max_time_uo[_iter]:                    # <=
                            sc_timed_t.append((_iter, t))
                        elif _iter in event_uo and t < max_time_uo[_iter]:         # 如果不加 _iter in event_uo 会出错         # <=
                            sc_timed_t.append((_iter, t))
                elif _iter in event_c and _iter in event_o:
                    # 可控可观事件
                    for current_node in current_state:
                        sc_uo_t = list(set(event_uo) & set(sc))
                        dfs_tree_t = dfs_events(iwa, sc_uo_t, event_uc=event_uc, event_uo=event_uo, source=current_node)  ## 待增加对环状结构的适应性

                        if not list(dfs_tree_t.nodes()).__len__():
                            # 如果很不幸, 这个时候dfs_tree是一个点
                            for edge_t in list(iwa.out_edges(current_node, data=True)):
                                if edge_t[2]['event'] == _iter:
                                    sc_timed_t.append((_iter, edge_t[2]['t_min']))                                      # 将可控可观事件的使能起始时间加入搜索栏
                                    t_interval.append(edge_t[2]['t_min'])                                               # Added
                        else:
                            # 如果这个时候dfs_tree不只是一个点
                            for node_t in list(dfs_tree_t.nodes()):
                                for edge_t in list(iwa.out_edges(node_t, data=True)):
                                    if edge_t[2]['event'] == _iter:
                                        t =  nx.shortest_path_length(dfs_tree_t, current_node, node_t)
                                        t += edge_t[2]['t_min']                                                         # 此时可观可控事件对应的使能时间应该是初始点到当前点最短时间 + 可观可控事件最短时间
                                        sc_timed_t.append((_iter, t))
                                        t_interval.append(t)                                                            # Added


                if sc_timed_t.__len__() != 0:
                    sc_event_tuple.append(sc_timed_t)       # 加入非空元素
                '''
                for t in t_interval:
                    if _iter not in event_uo and t >= min_time_uo[_iter] and t < max_time_uo[_iter]:                    # <=
                        sc_timed_t.append((_iter, t))
                    elif _iter in event_uo and t < max_time_uo[_iter]:         # 如果不加 _iter in event_uo 会出错         # <=
                        sc_timed_t.append((_iter, t))
                if sc_timed_t.__len__() != 0:
                    sc_event_tuple.append(sc_timed_t)       # 加入非空元素
                '''

            t_interval = list(set(t_interval))
            t_interval.sort()

            for i in range(0, sc_event_tuple.__len__()):
                sc_event_tuple[i] = list(set(sc_event_tuple[i]))

            sc_set = list(product(*sc_event_tuple))                 # https://blog.csdn.net/weixin_39652760/article/details/110774080
                                                                    # https://blog.csdn.net/liuqiang3/article/details/99707294
            sc_set = [list(_iter) for _iter in sc_set]              # tuple -> list
                                                                    # 而且最后拿到的数据是排序排好的，这里就不用考虑连接问题
            sc_set.sort()                                           # Critical

            for supervisor_curr in sc_set:
                ur = []                                             # unobservable reach, 对应论文中ur算子结果，即不可观事件可到达的集合
                ur_new = []

                sc_duration = []                                    # 单一使能时间->使能时间集合
                for sc_timed_t in supervisor_curr:
                    event_t = list(sc_timed_t)[0]

                    start_t = list(sc_timed_t)[1]
                    if t_interval.index(list(sc_timed_t)[1]) == t_interval.__len__() - 1:
                        end_t = float("inf")
                    else:
                        end_t = t_interval[t_interval.index(list(sc_timed_t)[1]) + 1]

                    if sc_timed_t[0] not in event_c:
                        for edge_t in dfs_tree.edges():                                                                               # 对于不可控事件, 打印policy的时候用他自己的区间打印
                            if dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['event'] == event_t:
                                t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_min']
                                t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_max']
                                if t_min == list(sc_timed_t)[1]:
                                    start_t = t_min
                                    end_t   = t_max

                    sc_duration.append((event_t, start_t, end_t))

                sc = [sc_ut[0] for sc_ut in supervisor_curr]

                for current_node in current_state:
                    try:
                        sc_uo_t = list(set(event_uo) & set(sc))
                        dfs_tree = dfs_events(iwa, sc_uo_t, event_uc, event_uo, current_node)                                       # dfs_events(iwa, sc_uo_t, event_uc, event_uo, current_node)
                        reachable_edge = list(dfs_ur(dfs_tree, supervisor_curr, event_uc, event_uo, source=current_node))

                        # edge -> 可达点
                        ur.append(current_node)
                        for edge_t in reachable_edge:
                            if dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event'] in event_uo:  # 只有不可观边能到达的才是ur,至于为什么不在dfs里处理，那是因为这么做会影响得到的决策数据
                                for sc_t in sc_duration:
                                    # CRITICAL
                                    '''
                                    if sc_t[0] == dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event'] and \
                                        (dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_min'] <= sc_t[1] and \
                                        dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_max'] >= sc_t[2]):       # Critical: 这里的时间是判断该点是否可以被使能
                                            ur.append(list(edge_t)[1])  # 可以发生transition的终点都是可达的点
                                    '''
                                    event_c_t = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event']
                                    if ((sc_t[0] == event_c_t and dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_min'] <= sc_t[1]) or
                                        (event_c_t in event_uc and event_c_t in event_uo)):             # 其实会发现有一个bug, 就是UR一定要从上一个状态算起, 假设当前是Z2, 那么就要从Z1到Z2算UR, 但是这里刚好利用了个换算的机制, 所有的UR都可以从当前的Y点算起, 所以只要计算从这个Y开始的绝对时间大于边的时间, 结果就是对的, 所以下面这个表达式才是对的, 上面那个有道理但是其实忽略了要从上一状态算起
                                            ur.append(list(edge_t)[1])  # 可以发生transition的终点都是可达的点
                        ur = list(set(ur))
                        ur.sort()
                    except KeyError:
                        # ur.append(current_node)
                        pass

                if ur.__len__() == 0:
                    z_state = (tuple(current_state), tuple(sc_duration))                                    # 5(Y)->5(Z)->5(Y)
                else:
                    z_state = (tuple(ur), tuple(sc_duration))
                if z_state == ((), ()):
                    continue

                is_state_listed = False                                                                     # 查找该点是否被list出来过
                is_state_listed_in_this_y = False
                for state_t in bts.nodes():
                    if state_type(z_state) == state_type(state_t) and \
                            state_t[0] == z_state[0] and \
                            set(get_policy_event(state_t)) == set(get_policy_event(z_state)):               # 可达点相同，不可观事件相同，但时间不同，则可认为该点listed
                        is_state_listed = True
                        try:
                            if nx.dijkstra_path_length(bts, current_state, state_t) >= 0:
                                is_state_listed_in_this_y = True
                                break
                        except:
                            pass

                if is_state_listed and is_state_listed_in_this_y:  # 如果这个点已经有过
                    node_to_update = []
                    for edge_t in bts.in_edges(state_t, data=True):
                        # 更新点
                        # bts.remove_node(edge_t[0])
                        # bts.add_node(z_state)

                        # 更新边
                        # bts.remove_node(edge_t[0], edge_t[1])
                        sc_last = bts.edge[edge_t[0]][edge_t[1]][0]['control']

                        event_last_list = []
                        for sc_timed_last in sc_last:
                            event_last_list.append(list(sc_timed_last)[0])

                        for sc_timed_t in supervisor_curr:
                            event_t = list(sc_timed_t)[0]
                            for sc_timed_last in sc_last:
                                event_last = list(sc_timed_last)[0]

                                # 如果这一个控制是存在的，那么则更新，扩大其时间区间
                                if event_t in event_last_list and event_t != event_last:
                                    continue
                                elif event_t in event_last_list and event_t == event_last:
                                    index = event_last_list.index(event_last)

                                    try:
                                        start_t = bts.edge[edge_t[0]][edge_t[1]][0]['control'][index][1]
                                    except:
                                        pass
                                    if t_interval.index(list(sc_timed_t)[1]) == t_interval.__len__() - 1:
                                        end_t = float("inf")
                                    else:
                                        end_t = t_interval[t_interval.index(list(sc_timed_t)[1]) + 1]
                                    if end_t > bts.edge[edge_t[0]][edge_t[1]][0]['control'][index][2]:

                                        # 这边是为了建立new_state_t，即更新了点edge_t[1]状态的点
                                        event_updated_t = list(edge_t[1][1])
                                        for i in range(0, event_updated_t.__len__()):
                                            if event_updated_t[i][0] == event_t:
                                                event_updated_t[i] = (event_t, start_t, end_t)
                                        new_state_t = (edge_t[1][0], tuple(event_updated_t))

                                        node_to_update.append((edge_t[0], edge_t[1], new_state_t))
                                        bts.edge[edge_t[0]][edge_t[1]][0]['control'][index] = (event_t, start_t, end_t)
                                        #nx.relabel_nodes(bts, {edge_t[1] : new_state_t})


                    for (old_origin, old_state, new_state) in node_to_update:
                        # 把edge_t[1]的边都转移到new_state_t上
                        bts.add_node(new_state)
                        for edge_t_t in bts.in_edges(old_state, data=True):
                            bts.add_edge(edge_t_t[0], new_state, control=edge_t_t[2]['control'])
                        for edge_t_t in bts.out_edges(old_state, data=True):
                            bts.add_edge(new_state, edge_t_t[1], control=edge_t_t[2]['control'])

                        bts.remove_node(old_state)
                        bts.add_edge(old_origin, new_state, control=tuple(event_updated_t))
                        #bts.edge[edge_t[0]][new_state_t][0]['control'][index] = (event_t, start_t, end_t)

                    # elif is_state_listed and not is_state_listed_in_this_y:     # 如果这个点对于当前y来说是全新的
                    #    pass
                else:

                    root_state = []
                    event_tz = get_policy_t_min(z_state)
                    event_tz_duration = get_policy_duration(z_state)        # 虽然这样有点蠢, 两个变量一样的
                    #t_max_t = copy.deepcopy(event_tz)
                    #for _iter in t_max_t.keys():
                    #    t_max_t[_iter] = -1             # 初始化，求最大时间
                    state_to_add_t = []

                    # ADDED
                    if z_state[1] == ():            # 无控制的点必然root_state是y_state
                        if not is_state_listed:
                            bts.add_node(z_state)
                            bts.add_edge(current_state, z_state, control=())
                        continue                     # 不用往下走了

                    # 找到 decision中，满足如下条件的所有点：
                    # Situation 1
                    #   1 事件完全相符
                    #   2 事件对应使能时间都比z_state小
                    #   3 满足1、2中， 每项使能时间对应最长 4 同一Y状态
                    #   4 同属于一个Y
                    # Situation 2
                    # 对于每一个branch的初始结点：如何判定？如果这个结点是他的初始结点, 则找不到一个时间相同, 且使能时间比他短的结点
                    #   1 当前点事件于余目标点事件, i.e., \forall \sigma' \in (\sigma', [t_1, t_2)), (\sigma', [t_1, t_2)) in q_z', (\sigma', [t_1, t_2)) \ in q_z
                    #   2 对应事件事件时间完全相等, q_z' = {(a,[1,2)), (uc,[4,5))} (目标点),       q_z = {(a,[1,2)), (b,[1,7)), (uc,[4,5))}(当前点)
                    #   3 找到满足条件1、2最小的一个点：注意 {(a,[2,3))}可能会同时连接到{(a,[2,3)), (b,[5,9)}和{(a,[2,3)), (b,[2,5))}

                    for state_t in bts.nodes():
                        try:
                            if not state_type(state_t) == 'Z_state' or not nx.dijkstra_path_length(bts, current_state, state_t) >= 0:   # 0 要求：找到的点和当前要增加的点都必须是在当前同一y状态之下:
                                continue
                        except:
                            continue

                        # Situation 1
                        event_t = get_policy_t_min(state_t)
                        if event_t.keys() == event_tz.keys():                                       # 1 事件完全相符
                            iter_num = 0
                            for _iter in event_t.keys():
                                if event_t[_iter] <= event_tz[_iter]:                               # 2 所有事件对应使能时间都比z_state小
                                    iter_num += 1
                            if iter_num == event_t.__len__():
                                # print(event_t, '\t', event_tz)
                                state_to_add_t.append(state_t)                                      # 3 满足1、2中，每箱使能时间对应最长, 先存起来, 然后统计
                                #for _iter in event_t.keys():
                                #    t_max_t[_iter] = event_t[_iter]                                # 3 满足1、2中，每箱使能时间对应最长

                        # Situation 2
                        event_t = get_policy_duration(state_t)
                        is_initial_node_of_a_branch = True
                        try:
                            if event_t.keys().__len__() == 0 or not nx.dijkstra_path_length(bts, current_state, state_t) >= 0:      # 0 state_t, 而且必须在同一个y顶点下
                                continue

                            # 首先判断z_state是不是初始结点
                            for state_t_t in bts.nodes():
                                try:
                                    if (not state_type(state_t_t) == 'Z_state' or state_t_t == z_state) or not nx.dijkstra_path_length(bts, current_state, state_t_t) >= 0: # 同理, 用来辅助判断的state_t_t必须是z状态, 而且必须在同一个y顶点下
                                        continue
                                except:
                                    continue

                                event_t_t = get_policy_duration(state_t_t)
                                if event_t_t.keys() == event_tz_duration.keys():
                                    for _iter in event_tz_duration.keys():
                                        if event_tz_duration[_iter][0] > event_t_t[_iter][0]:
                                            is_initial_node_of_a_branch = False
                                            break

                            if is_initial_node_of_a_branch:
                                event_t_num = 0
                                for _iter in event_t.keys():
                                    if _iter in event_tz_duration.keys() and event_t[_iter] == event_tz_duration[_iter]:
                                        event_t_num += 1
                                if event_t_num == event_t.__len__() and event_t.__len__() > 0:
                                    root_state.append(state_t)
                        except:
                            pass

                    # add states for situation 1
                    if state_to_add_t.__len__():
                        root_state.append(state_to_add_t[state_to_add_t.__len__() - 1])     # 3 满足1、2中，每箱使能时间对应最长, 这里讨了个巧, 因为所有的z状态都是根据policy排序的, 排序工作在之前就做好了, 所以这边直接取最后一个就行

                    # 增加点
                    if not is_state_listed:
                        bts.add_node(z_state)
                    # 增加边
                    if root_state.__len__() == 0:                                       # 如果点找不到，就是一定连接当前y_state的
                        bts.add_edge(current_state, z_state, control=sc_duration)
                    else:
                        for state_to_add_t in root_state:
                            bts.add_edge(state_to_add_t, z_state, control=sc_duration)
                    # 这里是将边，当前点，与根节点相连
                    # bts.add_edge(last_state, z_state, control=sc_duration)

                    # ITERATION
                    # last_state = z_state  # 迭代更新，因为前面edge都是排好的，所以这里直接加进来

        # 求NX
        # 现有思路：  针对每一个Z状态，求下一状态
        #           发现一个接一个，直接接在当前遍历的Z状态上
        #           问题就出在这边 发现一个接一个 ，这样得到的状态必然是分散的
        # 解决思路：
        state_to_add = []
        edge_to_add  = []
        for state_t in bts.nodes():
            # 对所有z_states 求NX
            y_state_w_observations = []

            if state_t not in visited and state_type(state_t) == 'Z_state':

                # 这边我是希望得到所有事件相同的点，最后再一起处理
                for node_t in state_t[0]:
                    for edge_t in list(iwa.out_edges(node_t, data=True)):
                        if edge_t[2]['event'] in event_o:     # 如果存在可到达的事件

                            for current_node in current_state:
                                dfs_tree = dfs_events(iwa, get_policy_event(state_t), event_uc, event_uo, current_node)
                                if not (node_t in dfs_tree.nodes() or current_node in dfs_tree.nodes()):
                                    continue

                                feasible_path = list(nx.all_simple_paths(dfs_tree, current_node, node_t))
                                if current_node == node_t and not feasible_path.__len__():
                                    feasible_path.append([current_node, node_t])                            # ADDED

                                if feasible_path.__len__() == 0:                                            # 如果没有可达路径，则重新查找，怎么可能没有可达路径
                                    continue

                                t_min = 1e6
                                t_max = -1
                                for path_t in feasible_path:
                                    if current_node == node_t and path_t == [current_node, node_t]:
                                        t_min_t = 0
                                        t_max_t = 0                                                         # ADDED
                                    else:
                                        last_node = path_t[path_t.__len__() - 2]
                                        t_min_t = dfs_tree.edge[last_node][node_t][0]['t_min']             # 因为dfs_tree里面会算好累加长度，所以这里只需调用
                                        t_max_t = dfs_tree.edge[last_node][node_t][0]['t_max']
                                    if t_min_t < t_min:
                                        t_min = t_min_t
                                    if t_max_t > t_max:
                                        t_max = t_max_t

                                if edge_t[2]['event'] not in event_c or \
                                   (edge_t[2]['event'] in event_c and edge_t[2]['event'] in get_policy_event(state_t) and \
                                        get_policy_duration(state_t)[edge_t[2]['event']][0] >= t_min + edge_t[2]['t_min']):     # 可观不可控，或：可观可控且被使能，且使能时间大于当前结点的最小时间
                                                                                                                                # 对可观可控事件，要求当前事件的使能最小时间要大于当前的最小观测时间
                                    # TODO：求解此处min-max时间
                                    t_min += edge_t[2]['t_min']
                                    t_max += edge_t[2]['t_max']

                                    y_state_w_observations.append((state_t, edge_t[0], edge_t[1], (edge_t[2]['event'], t_min, t_max)))      # 当前状态，IWA中当前状态中出发点{0}，IWA中当前状态可达点{1}，事件以及花的时间{2}    {0} -> {2} -> {1}

                if y_state_w_observations.__len__():

                    # 整理每一步得到的y_state
                    # Step 1: 取出所有事件和对应时间，做timeslice
                    nx_timeslice = {}
                    for y_t in y_state_w_observations:
                        if y_t[3][0] not in nx_timeslice.keys():            # y_t[3][0] 当前可观事件的事件名，如果当前可观事件未被记录
                            nx_timeslice.update({y_t[3][0]: [y_t[3][1], y_t[3][2]]})
                        else:
                            nx_timeslice[y_t[3][0]].append(y_t[3][1])
                            nx_timeslice[y_t[3][0]].append(y_t[3][2])

                        nx_timeslice.update({y_t[3][0]: list(set(nx_timeslice[y_t[3][0]]))})        # 去除相同项
                        nx_timeslice[y_t[3][0]].sort()                                              # 排序

                    # Step 2: 对每一时间段，求解当前的可达点
                    for event_t in nx_timeslice:
                        for i in range(0, nx_timeslice[event_t].__len__() - 1):
                            t1 = nx_timeslice[event_t][i]                                                   # 取出相邻的时间
                            t2 = nx_timeslice[event_t][i + 1]

                            state_to_add_t = []
                            for y_t in y_state_w_observations:
                                if y_t[3][0] == event_t and (y_t[3][1] <= t1 and y_t[3][2] >= t2):          # 当前遍历到的observation事件相等
                                    if y_t[2] not in state_to_add_t:
                                        state_to_add_t.append(y_t[2])                                       # 把可达点加入

                            state_to_add_t.sort()                                                           # 排序
                            if tuple(state_to_add_t) not in state_to_add:                                   # 对于当前事件event_t和t1, t2，所有可达点组成新的y状态
                                state_to_add.append(tuple(state_to_add_t))                                  # 如果该状态之前没被考虑过，加入

                                visited.append(tuple(state_to_add_t))
                                y_stack.append(tuple(state_to_add_t))

                            is_edge_added = False
                            index_ea = None
                            for edge_to_add_t in edge_to_add:
                                if edge_to_add_t[0] == y_t[0] and edge_to_add_t[1] == tuple(state_to_add_t) and \
                                   event_t == edge_to_add_t[2][0] and \
                                   (t1 == edge_to_add_t[2][2] or t2 == edge_to_add_t[2][1]):                # 查找即将增加的nx内, 有没有考虑过当前的情况,  关键，时间一定要相接
                                    is_edge_added = True
                                    index_ea = edge_to_add.index(edge_to_add_t)
                            if not is_edge_added:
                                edge_to_add.append((y_t[0], tuple(state_to_add_t), (event_t, t1, t2)))      # 如果当前边没有被考虑过，则添加
                                visited.append(y_t[0])
                            else:                                                                           # 如果有起点相同，终点相同，且时间相接的边，则合并，例子见下
                                t1 = min(t1, edge_to_add[index_ea][2][1])                                   # ('o1', 7, 13) ('o1', 13, 16))
                                t2 = max(t2, edge_to_add[index_ea][2][2])
                                edge_to_add[index_ea] = (y_t[0], tuple(state_to_add_t), (event_t, t1, t2))

        for index in range(0, state_to_add.__len__()):      # dictionary changed size during iteration
            try:
                bts.add_node(state_to_add[index])
            except:
                pass

        edge_to_remove = []
        for index in range(0, edge_to_add.__len__()):      # dictionary changed size during iteration
            # 为了合并状态, 这里其实可以检查一下之前的状态
            for edge_to_update in list(bts.in_edges(edge_to_add[index][1], data=True)):
                if edge_to_update[0] == edge_to_add[index][0]:
                    if edge_to_update[2]['observation'][0] == edge_to_add[index][2][0]:                    # 查看y状态之前的in_edge, 检查有没有起始点相同的状态, 以及观测事件相同
                        t_1_original = edge_to_update[2]['observation'][1]
                        t_2_original = edge_to_update[2]['observation'][2]
                        t_1 = edge_to_add[index][2][1]
                        t_2 = edge_to_add[index][2][2]
                        rst = intervalIntersection([[t_1_original, t_2_original]], [[t_1, t_2]])
                        if not rst.__len__():                                                              # 如果结果非空
                            edge_to_remove.append(edge_to_update)
                            edge_to_add[index][2] = (edge_to_add[index][2][0], min(t_1_original, t_1), max(t_2_original, t_2))


        for index in range(0, edge_to_remove.__len__()):
            bts.remove_edge(edge_to_remove[index][0], edge_to_remove[index][1])

        for index in range(0, edge_to_add.__len__()):  # dictionary changed size during iteration
            bts.add_edge(edge_to_add[index][0], edge_to_add[index][1], observation=edge_to_add[index][2])



    # 全部算完以后, 再最后做一个trim的工作
    # 第一步是删除所有重复的边
    edge_all = list(bts.edges())
    cntr_repeat_edges = dict(Counter(edge_all))
    #print(cntr_repeat_edges)
    for edge_t in cntr_repeat_edges.keys():
        for i in range(0, cntr_repeat_edges[edge_t] - 1):
            bts.remove_edge(edge_t[0], edge_t[1])


    # 第二步是trim
    edge_all = list(bts.edges())
    for edge_t in edge_all:
        if state_type(edge_t[0]) == 'Z_state' and state_type(edge_t[1]) == 'Z_state':
            ur_current = edge_t[0][0]
            policy_z1 = get_policy_duration(edge_t[0])
            policy_z2 = get_policy_duration(edge_t[1])
            for gamma_z1 in policy_z1.keys():
                policy_z1[gamma_z1] = list(policy_z1[gamma_z1])                         # tuple -> list

            for gamma_z1 in policy_z1.keys():
                if gamma_z1 in policy_z2.keys():
                    if policy_z1[gamma_z1][1] > policy_z2[gamma_z1][1]:                # trim的关键 解决原来那个(b, 1, 16) -> (b, 1, 7)的问题
                        policy_z1[gamma_z1][1] = policy_z2[gamma_z1][1]

            gamma_t = []
            for sigma_t in policy_z1.keys():
                gamma_t.append((sigma_t, policy_z1[sigma_t][0], policy_z1[sigma_t][1]))           # list -> tuple

            new_state = (ur_current, tuple(gamma_t))
            if tuple(gamma_t) == edge_t[0][1] or new_state in visited:
                continue                                                                 # 如果没变化就不用改了

            # 找到根节点
            root_node = []
            for edge_t_t in list(bts.in_edges(edge_t[0])):
                if edge_t_t[0] not in root_node:
                    root_node.append(edge_t_t[0])

            # 找到叶子节点
            leaf_node = []
            for edge_t_t in list(bts.out_edges(edge_t[0])):
                if edge_t_t[1] not in leaf_node:
                    leaf_node.append(edge_t_t[1])

            bts.add_node(new_state)
            visited.append(new_state)

            for node_t in root_node:
                bts.add_edge(node_t, new_state, control=tuple(gamma_t))

            for node_t in leaf_node:
                bts.add_edge(new_state, node_t, control=node_t[1])
            try:
                bts.remove_node(edge_t[0])
            except:
                pass

    return bts
