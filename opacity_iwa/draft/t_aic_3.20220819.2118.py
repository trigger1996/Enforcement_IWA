# -*- coding:utf-8 -*-
import networkx as nx
import io
import yaml
import copy
from itertools import combinations, product
from heapq import heappush, heappop
from itertools import count
from collections import Counter
import functools

import matplotlib.pyplot as plt

def sort_timeslice(elem):
    return elem[0]

def sort_root_state(x, y):
    if x[1] > y[1]:
        return 1
    elif x[1] < y[1]:
        return -1
    else:
        if x[2] > y[2]:
            return 1
        elif x[2] < y[2]:
            return -1
        else:
            return 0


class t_bts():
    def __init__(self, fin=None, source=None, event_c=None, event_o=None, event_uc=None, event_uo=None):
        self.event_uo = []
        self.event_o = []
        self.event_c = []
        self.event_uc = []

        self.iwa = nx.MultiDiGraph()
        self.init_state = []

        self.t_bts = nx.MultiDiGraph()

        if event_c != None and event_o != None and event_uc != None and event_uo != None:
            self.set_events(event_c, event_o, event_uc, event_uo)

        if fin != None and source != None:
            self.load_from_yaml(fin, source)

    def load_from_yaml(self, fin, source):
        fin = open(fin, 'r')
        data = yaml.load(fin)

        for node_t in data['graph']['nodes']:
            if data['graph']['nodes'][node_t].__len__():
                self.iwa.add_node(node_t, prop='secret')
            else:
                self.iwa.add_node(node_t)
        for edge_t in data['graph']['edges']:
            event = edge_t[2]['event']
            t_min = edge_t[2]['t_min']
            t_max = edge_t[2]['t_max']
            self.iwa.add_edge(edge_t[0], edge_t[1], event=event, t_min=t_min, t_max=t_max)

        for _iter in source:
            self.init_state.append(_iter)

    def set_events(self, event_c, event_o, event_uc, event_uo):
        self.event_c = event_c
        self.event_o = event_o
        self.event_uc = event_uc
        self.event_uo = event_uo

    # main function
    def construct_T_BTS(self, source=None, event_uo=None, event_o=None, event_c=None, event_uc=None):

        '''

        \begin{algorithm}[h]
          \small
          %    \SetAlgoNoLine  %去掉之前的竖线
               \caption{Construct T-BTS}
               \label{Alg:TBTS}
                \KwIn{IWA $G = (Q, \Sigma, Q_{0}, T, \mu)$, controllable event set $\Sigma_c$, observable event set $\Sigma_o$.}
                \KwOut{Timed bipartite transition system $A$}


                  $y\_stack \leftarrow Q_0$\;
                  $visited  \leftarrow Q_0$\;

                  \While{$y\_stack$ not empty}{
                      $y \leftarrow y\_stack.pop()$\;

                      $\Gamma_c \leftarrow \emptyset$\;
                      \For{{\bf each}$\Sigma_c' \subseteq 2^{\Sigma_c}$}{
                        $B \leftarrow Dfs\_Tree(G, y, \Sigma_c')$\;
                        $\{(\sigma_k, [t_i, t_j)) \vert i, j, k \in \mathbb{N}\} = \Sigma_c' \times Timeslice(B)$\;
                        $\Gamma_c \leftarrow \Gamma_c \cup \{(\sigma_k, [t_i, t_j)) \vert i, j, k \in \mathbb{N}\}$\;
                      }
                      \For{{\bf each}$(\sigma_k, [t_i, t_j)) \in \Gamma_c$}{
                          $\{q_z\} \leftarrow UR_{\{(\sigma_k, [t_i, t_j))\}}(y)$\;
                          $z \leftarrow (\{q_z\}, \{(\sigma_k, [t_i, t_j))\})$\;
                          \eIf{$\exists t_i', t_j' \in \mathbb{R}: z '' = (\{q_z\}, \{(\sigma_k, [t_i', t_j'))\}) \in A$}{                  %% 可达点相同, 事件相同, 但使能时间不同
                              $z'' \leftarrow (\{q_z\}, \{(\sigma_k, [\min(t_i, t_i') , \max(t_j, t_j')))\})$\;
                              \For{{\bf each}$(z', \{(\sigma_k, [t_i', t_j'))\}, z'') \in A$} {
                                  $(z', \{(\sigma_k, [t_i', t_j'))\}, z'') \leftarrow (z', \{(\sigma_k, [\min(t_i, t_i'), \max(t_j, t_j')))\}, z'')$\;
                              }
                              $visited  \leftarrow z''$\;
                          } {
                              % Else
                              Add state $z$ to $A$\;
                              $visited  \leftarrow z$\;
                              $Z' \leftarrow \{ (\{q_z'\}, \gamma) \vert \exists q_z' \in Q_t, Q_t \in Dfs\_Tree(G, y, \Sigma_c), \{\gamma \subsetneqq \{(\sigma_k, [t_i, t_j))\}\}$\;       % 找到使能相同, 但是使能时间比当前z小, 且具有最大t_max时间的z
                              Find $z_{max}$ s.t.  $z_{max} \in Z'$ : $\forall (\{q_z\}, \{(\sigma_k, [t_{i,k}, t_{j,k}))\}) \in Z'$, $\exists (\sigma_k, [t_{i,k}, t_{j,k}')) \in z_{max} : t_{j,k}' \geq t_{j,k}$\;

                              \eIf{$z'$ not exist} {
                                  Add transition $(y, (\sigma_o, \{(\sigma_k, [t_i, t_j))\}, z)$ to $A$\;
                              } {
                                  Add transition $(z', (\sigma_o, \{(\sigma_k, [t_i, t_j))\}, z)$ to $A$\;
                              }
                           }

                      }
                      % 求NX
                      \For{{\bf each} $z \in A$}{
                          \If{$z \notin visited$} {
                            $(y', (\sigma_o, [t_{yz,1}, t_{yz,2}))) \leftarrow NX^*(z, \{(\sigma_k, [t_i, t_j)) \vert i, j, k \in \mathbb{N}\})$\;            %% 直接用一个NX^*算子定义了所有
                          }
                          \If{$y' \notin A$}{
                              $Y \leftarrow y'$\;
                              $y\_stack \leftarrow y'$\;
                              $visited  \leftarrow y'$\;
                          }
                          Add transition $(z, (\sigma_o, [t_{yz,1}, t_{yz,2})), y')$ to $A$\;      %% 这里有问题, observation是什么没说
                      }
                  }
        \end{algorithm}

        :param source:
        :param event_uo:
        :param event_o:
        :param event_c:
        :param event_uc:
        :return:
        '''

        if event_c != None and event_o != None and event_uc != None and event_uo != None:
            self.set_events(event_c, event_o, event_uc, event_uo)
        if source != None:
            self.init_state.clear()

            for _iter in source:
                self.init_state.append(_iter)

        y_stack = []
        visited = []

        y_stack.append(tuple(self.init_state))
        visited.append(tuple(self.init_state))

        self.t_bts.add_node(tuple(self.init_state))

        while y_stack:
            current_state = y_stack.pop()
            visited.append(current_state)
            t_interval = []

            # finding the subset of Sigma_c
            events_2c = []
            for index in range(list(self.event_c).__len__()):
                for subset_t in combinations(list(self.event_c), index + 1):
                    events_2c.append(list(subset_t))

            sc_timed = []

            for current_node in current_state:

                for sc in events_2c:

                    # for debugging
                    if sc == ['a', 'b', 'o3']:
                        print(233)

                    B = self.dfstree(self.iwa, sc, event_uc=self.event_uc, event_uo=self.event_uo, source=current_node)

                    # get all time intervals from DfsTree
                    #t_interval = list(set(t_interval) | set(self.timeslice(B)))
                    t_interval = self.timeslice(B)
                    t_interval.sort(key=sort_timeslice)

                    # get all combinations of events, e.g. ('a',), ('b',), ('a', 'b')
                    _2_sc = []
                    for index in range(list(sc).__len__()):
                        for subset_t in combinations(list(sc), index + 1):
                            _2_sc.append(list(subset_t))

                    # policies = events + time intervals
                    # gain policies: e.g. (('a', (5, 7)), ('b', (1, 2)), ('o3', (2, 4)))
                    sc_t_current = []
                    for _2_sc_t in _2_sc:
                        sc_temp = self.assign_intervals_to_policies(_2_sc_t, t_interval)
                        for policy_t in sc_temp:
                            if type(policy_t[0]) == str:
                                sc_t_current.append((policy_t, ))         # put singular policy to a list such that it can be treated like policy: (('a', (1, 2)), ('b', (7, 11)))
                            else:
                                sc_t_current.append(policy_t)


                    # additional
                    # get all minimal-maximal time for the events in a DfsTree
                    [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree(B)

                    # remove all improper timing policies
                    policy_to_remove = []
                    for policy_t in sc_t_current:
                           for policy_index in list(policy_t):
                               event_t = policy_index[0]
                               t_i = policy_index[1][0]
                               t_j = policy_index[1][1]
                               if event_t not in sc_t_max.keys() or \
                                  t_i < sc_t_min[event_t] or t_j > sc_t_max[event_t]:       # event_t not in sc_t_max.keys() -> our picked policy may be inaccessible in dfstree B
                                   policy_to_remove.append(policy_t)

                    for sc_temp in sc_t_current:
                        for policy_t in policy_to_remove:
                            try:
                                sc_t_current.remove(policy_t)
                            except:
                                pass

                    # obtain policies from different nodes in Y
                    sc_timed = list(set(sc_timed + sc_t_current))
                    sc_timed.sort()

            # obtain Unobservable reaches
            for policy_t in sc_timed:

                    z_state_t = self.unobservable_reach(current_state, policy_t)


                    # check the existence for current z_state
                    # if a z-state is listed:
                    #   1 the unobservable reach is identical
                    #   2 the events in policies are identical
                    #   3 the policies of controllable & observable events are identical (time must be identical)
                    #   4 is originated from the same Y-state
                    [is_z_state_listed, z_state_prime] = self.is_state_listed(z_state_t, current_state)                 # [is_listed, original_state_in_t_bts]

                    if is_z_state_listed:

                        policy_extended = self.conjunction_of_policies(z_state_t[1], z_state_prime[1])
                        z_state_extended = (z_state_t[0], policy_extended)

                        self.replace_node_in_bts(z_state_prime, z_state_extended)

                        # for debugging
                        if z_state_prime == z_state_extended:
                            print(str(z_state_prime), str(z_state_t), str(z_state_extended))

                    else:
                        # find a root node, and then add the new Z-state to T-BTS
                        # the root node must satisfy
                        # 1 is from the same y-state
                        # 2 the set of event is no more than the new Z-state
                        # 3 the time of shared state must be smaller than the new Z-state
                        # 4 find all states satisfying 1 -- 3, and the first the number of event then the overall time should be maximized
                        root_state = self.find_root_state_for_z_states(current_state, z_state_t)
                        self.t_bts.add_edge(root_state, z_state_t, control=z_state_t[1])


            # solving NX
            '''
                Data structure: 
                [ (z_state_1, (state_1, state_2, ...), (event_t_1, t_1, t_2)),
                  (z_state_2, (state_3, ), (event_t_2, t_3, t_4)),  
                  ...
                 ]

            '''
            nx_edge_to_add = []

            for state_2_nx in self.t_bts.node:

                # obtaining NX for newly-added Z-states
                if not (self.state_type(state_2_nx) == 'Z_state' and state_2_nx not in visited):
                    continue

                y_state_nx_star = self.observable_reach_star(state_2_nx, current_state)
                for nx_w_observation in y_state_nx_star:
                    y_state_t = nx_w_observation[0]
                    policy_t  = nx_w_observation[1]
                    nx_edge_to_add.append((state_2_nx, y_state_t, policy_t))

                visited.append(state_2_nx)

            for nx_w_observation in nx_edge_to_add:
                z_state_t = nx_w_observation[0]
                y_state_t = nx_w_observation[1]
                event_t   = nx_w_observation[2][0]
                t_min     = nx_w_observation[2][1][0]
                t_max     = nx_w_observation[2][1][1]

                self.t_bts.add_edge(z_state_t, y_state_t, observation=(event_t, t_min, t_max))

                if y_state_t not in y_stack:
                    y_stack.append(y_state_t)

            print('iter completed once!')

        print(233)

    def get_event_from_policy(self, policy):
        policy_events = []
        for policy_t in policy:
            policy_events.append(policy_t[0])
        return policy_events

    def get_policy_event(self, state):
        policy_events = []
        for policy_t in state[1]:       ## 后面要改成state[2]
            policy_events.append(policy_t[0])
        return policy_events

    def get_policy_w_time(self, state):

        '''
        data structure
        state = ((q_1, q_2, ...), ((event_1, (t_1, t_2)), (event_2, (t_3, t_4)), ..., (event_i, (t_m, t_n)), ..., (event_1, (t_1', t_2')), ...)

        policy = { event : [[t_1, t_2], [t_3, t_4], ...] }

        e.g.:
        state_1  = (('1', '2',), ('a', (1, 2)), ('b', (4, 5)), ('a', (5, 7)))
        policy_1 = { a : [[1, 2], [5, 7]],
                     b : [[4, 5]]
                   }
        '''
        policy = {}
        for policy_t in state[1]:
            event_t = policy_t[0]
            t_1 = policy_t[1][0]
            t_2 = policy_t[1][1]
            if event_t not in policy.keys():
                policy.update({event_t : [[t_1, t_2]]})
            else:
                t_list = policy[event_t]
                t_list.append([t_1, t_2])
                policy.update({event_t, t_list})

        return policy

    def get_policy_dict(self, policy_in):

        '''
        data structure
        policy = { event : [[t_1, t_2], [t_3, t_4], ...] }
        '''
        policy_dict = {}
        for policy_t in policy_in:
            event_t = policy_t[0]
            t_1 = policy_t[1][0]
            t_2 = policy_t[1][1]
            if event_t not in policy_dict.keys():
                policy_dict.update({event_t : [[t_1, t_2]]})
            else:
                t_list = policy_dict[event_t]
                t_list.append([t_1, t_2])
                policy_dict.update({event_t, t_list})

        return policy_dict

    def state_type(self, state):
        if type(state[0]) == tuple and list(state).__len__() == 2:      ## 先用2，后面要记得改成3，判断方式也要细改一下
            return 'Z_state'
        else:
            return 'Y_state'

    def dfs_edges(self, G, event_list, event_uc, event_uo, source=None, depth_limit=None):
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

    def dfstree(self, iwa, event_list, event_uc, event_uo, source):
        edges = list(self.dfs_edges(iwa, event_list, event_uc, event_uo, source))

        G0 = nx.MultiDiGraph()
        G0.add_node(source)

        for edge_t in edges:
            start = list(edge_t)[0]
            end   = list(edge_t)[1]
            try:
                event = iwa.edge[start][end][0]['event']
                #if event in event_list or (event in event_uo and event in event_uc):                                 # 计算路径长的时候不能过可观事件
                #
                # for debugging
                if (event in event_list and event in event_uo) or (event in event_uo and event in event_uc):
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
                t_min  = nx.shortest_path_length(G0, source, start, weight='t_min') + iwa.edge[start][end][0]['t_min']
                t_max = -nx.shortest_path_length(G0, source, start, weight='t_max') + iwa.edge[start][end][0]['t_max']
            except:
                pass

            dfs_tree.add_edge(start, end, event=event, t_min=t_min, t_max=t_max)

        # 到这里计算到的都是通过uo到达的最短路径
        # 那些可经由可达时间到达的点还没有做出来
        for edge_t in edges:
            start = list(edge_t)[0]
            end   = list(edge_t)[1]

        return dfs_tree

    def timeslice(self, dfs_tree):
        t_step = []
        t_interval = []
        for edge_t in  dfs_tree.edges():
            t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_min']
            t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_max']
            t_step.append(t_min)
            t_step.append(t_max)

        t_step = list(set(t_step))      # 排序，去除多余元素
        t_step.sort()
        for i in range(0, t_step.__len__() - 1):
            t_interval.append((t_step[i], t_step[i + 1]))
        #t_interval.sort(key=sort_timeslice)

        return t_interval

    def get_min_max_time_from_dfstree(self, B):
        # additional
        # get all minimal-maximal time for the events in a DfsTree
        sc_t_min = {}
        sc_t_max = {}
        for node_start in B.edge:
            for node_end in B.edge[node_start]:
                event_t = B.edge[node_start][node_end][0]['event']
                t_min = B.edge[node_start][node_end][0]['t_min']
                t_max = B.edge[node_start][node_end][0]['t_max']
                if event_t not in sc_t_min.keys():
                    sc_t_min.update({event_t: t_min})
                    sc_t_max.update({event_t: t_max})
                else:
                    if sc_t_min[event_t] > t_min:
                        sc_t_min[event_t] = t_min
                    if sc_t_max[event_t] < t_max:
                        sc_t_max[event_t] = t_max

        return [sc_t_min, sc_t_max]

    def assign_intervals_to_policies(self, events, t_interval):
        policy_list = []

        if events.__len__() == 1:
            for _iter in product(list(events), list(t_interval)):
                policy_list.append(_iter)
        else:
            policy_t = []
            for event_t in events:
                policy_index = []
                for _iter in product([event_t], list(t_interval)):
                    policy_index.append(_iter)
                policy_t.append(policy_index)

            for _iter in product(*policy_t):
                policy_list.append(_iter)

        return policy_list

    def conjunction_of_policies(self, policy_1, policy_2):
        policy = []

        # policy tuple to dict for better manipulation
        policy_dict_1 = self.get_policy_dict(policy_1)
        policy_dict_2 = self.get_policy_dict(policy_2)

        policy_dict = {}
        for event_t in policy_dict_1.keys():
            if event_t in policy_dict_2.keys():

                # if the event is shared
                # take all time interval in policy_1 and policy_2, then make conjunction for all time interval
                t_interval_list = list(policy_dict_1[event_t] + policy_dict_2[event_t])
                t_interval_conjuncted = []

                t_interval_conjuncted.append(t_interval_list.pop())

                while t_interval_list.__len__():
                    t_interval_to_merge = t_interval_list.pop()
                    t_min_1 = t_interval_to_merge[0]
                    t_max_1 = t_interval_to_merge[1]

                    for index in range(0, t_interval_conjuncted.__len__()):
                        t_interval_prime = t_interval_conjuncted[index]
                        t_min_2 = t_interval_prime[0]
                        t_max_2 = t_interval_prime[1]

                        # if the time interval is intersected
                        '''
                            |--    |    --  --    |    --  --    |    --|
                                t_min_1 --.... t_min_2 ....-- t_max_1
                        
                            |--    |    --  --    |    --  --    |    --|
                                t_min_2 --.... t_min_1 ....-- t_max_2                
                        
                        '''
                        if (t_min_1 <= t_min_2 and t_min_2 <= t_max_1) or \
                           (t_min_2 <= t_min_1 and t_min_1 <= t_max_2):
                            t_interval_conjuncted[index][0] = min(t_min_1, t_min_2)
                            t_interval_conjuncted[index][1] = max(t_max_1, t_max_2)
                        else:
                            t_interval_conjuncted.append([t_min_1, t_max_1])

                policy_dict.update({event_t: t_interval_conjuncted})

            else:
                # if the event is NOT shared, then directly add it to target dict
                policy_dict.update({event_t: policy_dict_1[event_t]})

        # check events in policy_2 again in case for missing
        for event_t in policy_dict_2.keys():
            if event_t not in policy_dict_1.keys():
                # if the event is NOT shared, then directly add it to target dict
                policy_dict.update({event_t: policy_dict_2[event_t]})


        # policy dict -> tuple
        for event_t in policy_dict.keys():
            t_list = policy_dict[event_t]
            for t_interval in t_list:
                t_min = t_interval[0]
                t_max = t_interval[1]
                policy.append((event_t, (t_min, t_max)))

        return tuple(policy)

    def unobservable_reach(self, current_state, policy):

        ur_node = []
        event_t = self.get_event_from_policy(policy)

        for current_node in current_state:
            ur_node.append(current_node)

            dfs_tree = self.dfstree(self.iwa, event_t, self.event_uc, self.event_uo, current_node)
            if dfs_tree.node.__len__():
                reachable_edge = list(self.dfs_ur(dfs_tree, policy, self.event_uc, self.event_uo, source=current_node))

                # for debugging
                # 不知道这个放在这里干嘛
                # [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree(dfs_tree)

                for edge_t in reachable_edge:
                    event_c_t = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event']
                    event_t_min = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_min']

                    is_control_policy_matched = False
                    for policy_t in policy:
                        if event_c_t in self.event_uo and \
                           ((event_c_t == policy_t[0] and event_t_min >= policy_t[1][0]) or \
                            (event_c_t in self.event_uc and event_c_t in self.event_uo)):
                            is_control_policy_matched = True
                    if is_control_policy_matched:
                        ur_node.append(list(edge_t)[1])

            ur_node = list(set(ur_node))
            ur_node.sort()

        z_state = (tuple(ur_node), tuple(policy))
        return z_state

    def dfs_ur(self, dfs_tree, sc, event_uc, event_uo, source=None, depth_limit=None):
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

                    is_edge_reachable = False  # added
                    for sc_t in sc:
                        event_t = list(sc_t)[0]
                        event_c_t = dfs_tree.edge[parent][child][0]['event']
                        t = list(sc_t)[1][0]
                        if ((event_t == event_c_t and dfs_tree.edge[parent][child][0]['t_min'] <= t and \
                             event_t == event_c_t and dfs_tree.edge[parent][child][0]['t_max'] >  t) or
                            (event_c_t in event_uc and event_c_t in event_uo)):
                            is_edge_reachable = True
                            break
                    if not is_edge_reachable:
                        continue

                    if str([parent, child]) not in visited:  # 因为list本身不可哈希，所以用str(list())来代替list
                        yield parent, child  # yield parent, child 这个版本的python没法调试yield  https://zhuanlan.zhihu.com/p/268605982
                        visited.add(str([parent, child]))  # visited.add(child)
                        if depth_now > 1:
                            stack.append((child, depth_now - 1, iter(dfs_tree[child])))

                except StopIteration:
                    stack.pop()

    def observable_reach_star(self, z_state, current_y_state):
        if self.state_type(z_state) != 'Z_state' or self.state_type(current_y_state) != 'Y_state':
            raise AssertionError('Must input correct state type')

        state_ur        = z_state[0]
        policy          = z_state[1]
        event_in_policy = self.get_event_from_policy(policy)

        # dict for min-max time from current_y_states to nodes in z_state
        '''
        data structure:
            [ (iwa_state_1, t_min_1)),
              (iwa_state_2, t_min_2)), 
              ...
             ]
        '''
        min_time_dict = {}
        max_time_dict = {}

        # obtain min-max time by DfsTree
        for current_state in current_y_state:

            min_time_dict.update({current_state : 0})
            max_time_dict.update({current_state : 0})

            dfs_tree = self.dfstree(self.iwa, event_in_policy, self.event_uc, self.event_uo, current_state)
            if dfs_tree.node.__len__():
                reachable_edge = list(self.dfs_ur(dfs_tree, policy, self.event_uc, self.event_uo, source=current_state))

                # for debugging
                # 不知道这个放在这里干嘛
                # [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree(dfs_tree)

                for edge_t in reachable_edge:
                    edge_end  = edge_t[1]
                    event_c_t = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event']
                    event_t_min = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_min']
                    event_t_max = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_max']

                    for policy_t in policy:
                        if event_c_t in self.event_uo and \
                           ((event_c_t == policy_t[0] and event_t_min >= policy_t[1][0]) or \
                            (event_c_t in self.event_uc and event_c_t in self.event_uo)):
                            # min-time
                            if edge_end not in min_time_dict.keys():
                                min_time_dict.update({edge_end : event_t_min})
                            elif min_time_dict[edge_end] > event_t_min:
                                    min_time_dict.update({edge_end: event_t_min})

                            # max-time
                            if edge_end not in max_time_dict.keys():
                                max_time_dict.update({edge_end : event_t_max})
                            elif max_time_dict[edge_end] < event_t_max:
                                    max_time_dict.update({edge_end: event_t_max})


        # observable reach with policies
        '''
        data structure:
            { event_1 : [(state_1, (t_1, t_2)), (state_2, (t_3, t_4)), ...],
              event_2 : [(state_3, (t_5, t_6)), ...],
              ...            
            }

        '''
        nx_star_un_merged = {}

        for state_t in state_ur:            # the keys of min_time_dict / max-time_dict must be identical to STATE_UR

            # for debugging
            if state_t == '3':
                print(233)

            reachable_edge_nx = self.iwa.out_edges(state_t, data=True)
            for edge_t in reachable_edge_nx:
                edge_start  = edge_t[0]
                edge_end    = edge_t[1]
                event_t     = edge_t[2]['event']
                event_t_min = edge_t[2]['t_min']
                event_t_max = edge_t[2]['t_max']
                if event_t in self.event_o and \
                   (event_t in self.event_uc or \
                    (event_t in self.event_c and event_t in event_in_policy)):

                    event_t_min = event_t_min + min_time_dict[edge_start]
                    event_t_max = event_t_max + max_time_dict[edge_start]

                    if event_t not in nx_star_un_merged.keys():
                        nx_star_un_merged.update({event_t : [(edge_end, (event_t_min, event_t_max))]})
                    else:
                        nx_star_un_merged[event_t].append((edge_end, (event_t_min, event_t_max)))

        '''
            nx_star: Data structure: 
            [ ((state_1, state_2, ...), (event_t_1, t_1, t_2)),
              ((state_3, ), (event_t_2, t_3, t_4)),  
              ...
             ]

        '''
        nx_star = self.setprate_nx_star(nx_star_un_merged)

        return nx_star

    def setprate_nx_star(self, nx_star_un_merged):

        # if a event can be observed through 2 OR MORE EDGES?
        # then it should be merged / separated
        # e.g.:  [('5', ('o3', 6, 16)), ('6', ('o3', 9, 20))] -->
        #        [('5', ('o3', 6, 9)), (('5', '6'), ('o3', 9, 16)), ('6', ('o3', 9, 20))]
        '''
            Data structure: 
            [ ((state_1, state_2, ...), (event_t_1, t_1, t_2)),
              ((state_3, ), (event_t_2, t_3, t_4)),  
              ...
             ]

        '''
        nx_star = []

        for event_t in nx_star_un_merged.keys():
            if nx_star_un_merged[event_t].__len__() == 1:
                state_t = nx_star_un_merged[event_t][0][0]
                t_min   = nx_star_un_merged[event_t][0][1][0]
                t_max   = nx_star_un_merged[event_t][0][1][1]

                nx_star.append((tuple(state_t), (event_t, (t_min, t_max))))
            else:
                '''
                    nx_temp: Data structure: 
                    [ ((state_1, state_2, ...), (event_t_1, t_1, t_2)),
                      ((state_3, ), (event_t_2, t_3, t_4)), 
                      ...
                     ]
                '''
                nx_temp = []
                t_instant = []

                # extract all time instant
                for nx_w_time_t in nx_star_un_merged[event_t]:
                    t_instant.append(nx_w_time_t[1][0])          # t_min
                    t_instant.append(nx_w_time_t[1][1])          # t_max
                t_instant = list(set(t_instant))
                t_instant.sort()

                # check all time instant for all reachable state
                for i in range(0, t_instant.__len__() - 1):
                    t_i      = t_instant[i]
                    t_i_next = t_instant[i + 1]
                    reachable_state = []

                    # merge / separated states within the same policy
                    for nx_w_time_t in nx_star_un_merged[event_t]:
                        state_t = nx_w_time_t[0]
                        t_min   = nx_w_time_t[1][0]
                        t_max   = nx_w_time_t[1][1]
                        if t_i >= t_min and t_i < t_max:
                            reachable_state.append(state_t)

                    # sort reachable state
                    reachable_state = list(set(reachable_state))
                    reachable_state.sort()

                    nx_temp.append((tuple(reachable_state), (event_t, (t_i, t_i_next))))

                nx_star = nx_star + nx_temp

        return nx_star

    def is_state_listed(self, z_state, current_state):
        is_state_listed = False
        is_listed_state_with_the_same_y = False

        for state_t in self.t_bts.node:
            #   1 the unobservable reach is identical
            #   2 the events in policies are identical
            #   3 the policies of controllable & observable events are identical (time must be identical)
            if self.state_type(z_state) == self.state_type(state_t) and \
                state_t[0] == z_state[0] and \
                set(self.get_policy_event(state_t)) == set(self.get_policy_event(z_state)) and \
                self.is_event_in_controlable_observable_policies_identical(self.get_policy_w_time(state_t), self.get_policy_w_time(z_state)):
                is_state_listed = True
                try:
                    #   4 is originated from the same Y-state
                    #   5 the cost is identical -> make sure state_t and z_state are the identical state
                    '''
                    if nx.dijkstra_path_length(self.t_bts, current_state, state_t) >= 0 and \
                       nx.dijkstra_path_length(self.t_bts, current_state, state_t) == nx.dijkstra_path_length(self.t_bts, current_state, z_state):
                    '''
                    # 这步错了（可能）, 有没有更好的办法
                    if nx.dijkstra_path_length(self.t_bts, current_state, state_t) >= 0:
                        is_listed_state_with_the_same_y = True
                        break
                    else:
                        # for debugging
                        is_listed_state_with_the_same_y = False
                except nx.NetworkXNoPath as e:
                    pass

        if is_state_listed and is_listed_state_with_the_same_y:
            return [True, state_t]
        else:
            return [False, None]

    def is_event_in_controlable_observable_policies_identical(self, policy, policy_prime):
        # the policies of controllable & observable events are identical (time must be identical)
        is_identical = False

        # first check whether there are controllable & observable events
        # if there is no controllable & observable events in designated policy, then return True
        is_no_controllable_observable_event = True
        for event_t in policy.keys():
            if event_t in self.event_c and event_t in self.event_o:
                is_no_controllable_observable_event = False
        if is_no_controllable_observable_event:
            return  True

        for event_t in policy.keys():
            # first check whether the event_t is shared && event_t is controllable and observable
            if (event_t in self.event_c and event_t in self.event_o) and \
                event_t in policy_prime.keys():
                # then extract all time interval in policy and policy_prime
                t_list       = policy[event_t]
                t_list_prime = policy_prime[event_t]
                for t_interval in t_list:
                    for t_interval_prime in t_list_prime:
                        # if there exist a time interval that is shared
                        if t_interval[0] == t_interval_prime[0] and t_interval[1] == t_interval_prime[1]:
                            is_identical = True

        return is_identical

    def replace_node_in_bts(self, node, node_prime):

        # for debugging
        if node == node_prime:
            return

        in_states = []
        out_states = []
        # find all in edges for current node
        for edge_start in self.t_bts.edge.keys():
            for edge_end_t in self.t_bts.edge[edge_start]:
                if edge_end_t == node:
                    in_states.append(edge_start)

        # find all out edges for current node
        for edge_end_t in self.t_bts.edge[node]:
            out_states.append(edge_end_t)

        # add new node to T-BTS
        self.t_bts.add_node(node_prime)
        # add connections for in nodes
        for node_t in in_states:
            self.t_bts.add_edge(node_t, node_prime, control=node_prime[1])          # the edge added must be Y->Z, or Z->Z for node_prime is a Z_state, then the properities MUST be CONTROL
        # add connections for out nodes
        for node_t in out_states:
            if self.state_type(node_t) == 'Y_state':
                observation_t = self.t_bts.edge[node][node_t][0]['observation']
                self.t_bts.add_edge(node_prime, node_t, observation=observation_t)
            elif self.state_type(node_t) == 'Z_state':
                self.t_bts.add_edge(node_prime, node_t, control=node_t[1])

        # finally, remove nodes
        self.t_bts.remove_node(node)

    def find_root_state_for_z_states(self, current_y_state, z_state):
        # find a root node, and then add the new Z-state to T-BTS
        # the root node must satisfy
        # 1 is from the same y-state
        # 2 the set of event is no more than the new Z-state
        # 3 the time of shared state must be smaller than the new Z-state
        # 4 find all states satisfying 1 -- 3, and the first the number of event then the overall time should be maximized
        root_state = current_y_state
        root_state_candidate = []

        for state_t in self.t_bts.node:
            if self.state_type(state_t) == 'Z_state':
                try:

                    # 1 is from the same y-state
                    if nx.dijkstra_path_length(self.t_bts, current_y_state, state_t) >= 0:                  # 这步错了（可能）, 如果current_y_state -> state_t不通, 则不属于同一y-state, 有没有更好的办法
                        event_state_t = set(self.get_policy_event(state_t))
                        event_z_state = set(self.get_policy_event(z_state))

                        # 2 the set of event is no more than the new Z-state
                        if event_state_t.issubset(event_z_state):

                            # 3 the time of shared state must be smaller than the new Z-state
                            policy_state_t_dict = self.get_policy_w_time(state_t)
                            policy_z_state_dict = self.get_policy_w_time(z_state)
                            is_all_time_interval_smaller = True

                            for event_t in policy_state_t_dict.keys():
                                # find all minimal & maximal time in policy_state_t & policy_z_state
                                t_list_1 = policy_state_t_dict[event_t]
                                t_min_1 = t_list_1[0][0]
                                t_max_1 = t_list_1[0][1]
                                for t_interval in t_list_1:
                                    t_min_prime = t_interval[0]
                                    t_max_prime = t_interval[1]
                                    if t_min_prime < t_min_1:
                                        t_min_1 = t_min_prime
                                    if t_max_prime > t_max_1:
                                        t_max_1 = t_max_prime

                                t_list_2 = policy_z_state_dict[event_t]
                                t_min_2 = t_list_2[0][0]
                                t_max_2 = t_list_2[0][1]
                                for t_interval in t_list_2:
                                    t_min_prime = t_interval[0]
                                    t_max_prime = t_interval[1]
                                    if t_min_prime < t_min_2:
                                        t_min_2 = t_min_prime
                                    if t_max_prime > t_max_2:
                                        t_max_2 = t_max_prime

                                if not (t_min_1 <= t_min_2 and t_max_1 <= t_max_2):
                                    is_all_time_interval_smaller = False
                                    break

                            if is_all_time_interval_smaller:
                                root_state_candidate.append(state_t)

                except nx.NetworkXNoPath as e:
                    pass

        # 4 find all states satisfying 1 -- 3, and the first the number of event then the overall time should be maximized
        if root_state_candidate.__len__():
            candidate_event_time = []           # data structure: [Z_state, number_of_events, time]
            for state_t in root_state_candidate:
                # number of events
                number_of_events = self.get_policy_event(state_t).__len__()

                # time
                # take the maximal time into account
                policy_state_t_dict = self.get_policy_w_time(state_t)
                time_t = 0
                for event_t in policy_state_t_dict.keys():
                    t_list = policy_state_t_dict[event_t]
                    t_max = t_list[0][1]
                    for t_interval in t_list:
                        t_max_prime = t_interval[1]
                        if t_max_prime > t_max:
                            t_max = t_max_prime                 # find the maximal time in all the time interval from event_t

                    time_t += t_max

                #
                candidate_event_time.append([state_t, number_of_events, time_t])

            candidate_event_time.sort(key=functools.cmp_to_key(sort_root_state), reverse=True)
            root_state = candidate_event_time[0][0]
        else:
            root_state = current_y_state

        return root_state

    def assign_node_colors(self, init_marker_rgb='#DC5712', y_state_rgb='#83AF9B', z_state_rgb='#FE4365'):
        values = []
        for node_t in self.t_bts.nodes():
            if node_t == ('init',):
                values.append(init_marker_rgb)
            elif self.state_type(node_t) == 'Z_state':
                values.append(z_state_rgb)
            else:
                values.append(y_state_rgb)
        return values

    def plot(self, init_marker_rgb='#DC5712', y_state_rgb='#83AF9B', z_state_rgb='#FE4365', is_show=True):
        self.t_bts.add_edge(('init',), tuple(self.init_state))
        node_color = self.assign_node_colors(init_marker_rgb, y_state_rgb, z_state_rgb)

        pos = nx.shell_layout(self.t_bts)  # nx.spectral_layout(bts) shell_layout spring_layout
        nx.draw(self.t_bts, pos=pos, with_labels=True, node_color=node_color, font_size=8.5)

        nx.draw_networkx_edge_labels(self.t_bts, pos, font_size=6.5)  # font_size=4.5

        if is_show:
            plt.show()
