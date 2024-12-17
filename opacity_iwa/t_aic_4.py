# -*- coding:utf-8 -*-
import networkx as nx
import yaml
from itertools import combinations, product
from utils import print_c
import functools
import basic.intervals as intervals

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
            if x[3] == 'closed' and y[3] == 'open':
                return 1
            elif x[3] == 'open' and y[3] == 'closed':
                return -1
            else:
                return 0

def sort_policies(t1, t2):
    # 比较长度
    len1, len2 = len(t1), len(t2)
    if len1 != len2:
        return len1 - len2  # 长度较短的元组排前面

    # 元素逐个比较
    for i in range(len1):
        e1, e2 = t1[i], t2[i]
        if isinstance(e1, tuple) and isinstance(e2, tuple):
            # 如果元素本身是元组，递归比较
            res = sort_policies(e1, e2)
        else:
            # 直接按元素值比较
            res = (e1 > e2) - (e1 < e2)

        if res != 0:
            return res

    return 0

class w_aic():
    def __init__(self, fin=None, source=None, event_c=None, event_o=None, event_uc=None, event_uo=None):
        self.event_uo = []
        self.event_o = []
        self.event_c = []
        self.event_uc = []

        self.iwa = nx.MultiDiGraph()
        self.init_state = []

        self.w_aic = nx.MultiDiGraph()

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
            event  = edge_t[2]['event']
            t_min  = edge_t[2]['t_min']
            t_max  = edge_t[2]['t_max']
            l_attr = edge_t[2]['l_attr']                        # 'closed' or 'open'
            r_attr = edge_t[2]['r_attr']                        # REMEMBER, 'open' not 'opened'
            self.iwa.add_edge(edge_t[0], edge_t[1], event=event, t_min=t_min, t_max=t_max, l_attr=l_attr, r_attr=r_attr)

        for _iter in source:
            self.init_state.append(_iter)

    def set_events(self, event_c, event_o, event_uc, event_uo):
        self.event_c = event_c
        self.event_o = event_o
        self.event_uc = event_uc
        self.event_uo = event_uo

    # main function
    def construct_W_AIC(self, source=None, event_uo=None, event_o=None, event_c=None, event_uc=None, t_cutoff=15):

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
        ur_list = {}                        # for recording all z state that originates from y state, including those replaced

        y_stack.append(tuple(self.init_state))
        visited.append(tuple(self.init_state))

        self.w_aic.add_node(tuple(self.init_state))

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

                    B = self.dfstree2(self.iwa, sc, event_uc=self.event_uc, event_uo=self.event_uo, source=current_node, t_cutoff=t_cutoff)

                    # get all time intervals from DfsTree
                    #t_interval = list(set(t_interval) | set(self.timeslice(B)))
                    t_interval = self.timeslice2(B, source=current_node)
                    t_interval.sort(key=sort_timeslice)

                    # for debugging
                    # if current_state == ('3', '7'):
                    #     print_c("current_state %s / %s | edgeNum_URTree: %d | intervalNum_TS: %d" % (str(current_node), str(current_state), B.number_of_edges(), t_interval.__len__(), ), color='bright_cyan', style='bold')

                    # get all combinations of events, e.g. ('a', 'b') -> ('a',), ('b',), ('a', 'b')
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
                    [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree(B, source=current_node)

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

                    for policy_t in policy_to_remove:
                        try:
                            sc_t_current.remove(policy_t)
                        except:
                            pass

                    # obtain policies from different nodes in Y
                    sc_timed.append(tuple())                            # added an empty tuple
                    sc_timed = list(set(sc_timed + sc_t_current))

            # for debugging
            for policy_d in sc_timed:
                for policy_d_i in policy_d:
                    if policy_d_i[1][1] > t_cutoff:
                        print_c("invalid policy ... %s, t > cutoff: %d" % (str(policy_d), t_cutoff,), color='bright_magenta', style='italic')

            print_c("current_state %s / sc_timed number: %d" % (str(current_state), sc_timed.__len__(),), color='cyan', style='bold')
            print_c("sc_timed: %s" % (str(sc_timed),), color='yellow')
            sc_timed.sort(key=functools.cmp_to_key(sort_policies))

            # for debugging
            if current_state == ('3', '7'):
                debug_var = 1

            # obtain Unobservable reaches
            for policy_t in sc_timed:
                z_state_t = self.unobservable_reach(current_state, policy_t, t_cutoff=t_cutoff)

                # added
                if z_state_t == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (4, 5.0, 'closed', 'open')))):
                    debug_var = 2

                # check the existence for current z_state
                # if a z-state is listed:
                #   1 the unobservable reach is identical
                #   2 the events in policies are identical
                #   3 the policies of controllable & observable events are identical (time must be identical)
                #   4 is originated from the same Y-state
                #   5 20230606: for successive states, the ending time of control policy must not be larger
                [is_z_state_listed, z_state_prime] = self.is_state_listed(z_state_t, current_state, ur_list)                            # [is_listed, original_state_in_t_bts]

                if z_state_t == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (4, 5.0, 'closed', 'open')))):
                    if z_state_t not in visited:
                        debug_var = 2

                if z_state_t not in visited:                                                                                          # 20230606 Added
                # if True:                                                                                                                # can be enabled for debugging
                    if is_z_state_listed:

                        policy_extended = self.conjunction_of_policies(z_state_t[1], z_state_prime[1])
                        z_state_extended = (z_state_t[0], policy_extended)

                        self.replace_node_in_bts(z_state_prime, z_state_extended)

                        if current_state not in ur_list.keys():
                            ur_list[current_state] = [ z_state_extended ]
                        else:
                            ur_list[current_state].append(z_state_extended)
                        ur_list[current_state] = list(set(ur_list[current_state]))
                    else:
                        # find a root node, and then add the new Z-state to T-BTS
                        # the root node must satisfy
                        # 1 is from the same y-state
                        # 2 the set of event is no more than the new Z-state
                        # 3 the time of shared state must be smaller than the new Z-state
                        # 4 find all states satisfying 1 -- 3, and the first the number of event then the overall time should be maximized
                        if current_state not in ur_list.keys():
                            ur_list_current = []
                        else:
                            ur_list_current = ur_list[current_state]

                        root_state = self.find_root_state_for_z_states(current_state, z_state_t, ur_list_current)
                        self.w_aic.add_edge(root_state, z_state_t, control=z_state_t[1])

                        if current_state not in ur_list.keys():
                            ur_list[current_state] = [ z_state_t ]
                        else:
                            ur_list[current_state].append(z_state_t)
                        ur_list[current_state] = list(set(ur_list[current_state]))

                    # for debugging
                    debug_state_t = (('3', '5', '7'), (('a', (2.5, 7)), ('b', (7, 10))))
                    try:
                        if z_state_t == debug_state_t or z_state_extended == debug_state_t:
                            debug_var = 5
                    except:
                        pass

            # solving NX
            '''
                Data structure: 
                [ (z_state_1, (state_1, state_2, ...), (event_t_1, t_1, t_2)),
                  (z_state_2, (state_3, ), (event_t_2, t_3, t_4)),  
                  ...
                 ]

            '''
            nx_edge_to_add = []

            for state_2_nx in self.w_aic.node:

                if state_2_nx == (('3', '7'), (('b', (4, 10)),)):
                    debug_var = 17

                # obtaining NX for newly-added Z-states
                if not (self.state_type(state_2_nx) == 'Z_state' and state_2_nx not in visited):
                    continue

                # for debugging
                if '7' in list(state_2_nx[0]):
                    debug_var = 6
                if state_2_nx == (('3', '5', '7'), (('a', (4, 7)),)):
                    debug_var = 7
                if state_2_nx == (('1', '2'), (('a', (1, 2)), ('o3', (3, 5.5)))):
                    debug_var = 18

                y_state_nx_star = self.observable_reach_star(state_2_nx, current_state, t_cutoff=t_cutoff)
                for nx_w_observation in y_state_nx_star:
                    y_state_t = nx_w_observation[0]
                    policy_t  = nx_w_observation[1]
                    nx_edge_to_add.append((state_2_nx, y_state_t, policy_t))

                    if y_state_t == tuple():
                        debug_var = 17

                visited.append(state_2_nx)

            for nx_w_observation in nx_edge_to_add:
                z_state_t = nx_w_observation[0]
                y_state_t = nx_w_observation[1]
                event_t   = nx_w_observation[2][0]
                t_min     = nx_w_observation[2][1][0]
                t_max     = nx_w_observation[2][1][1]
                l_attr    = nx_w_observation[2][1][2]
                r_attr    = nx_w_observation[2][1][3]

                self.w_aic.add_edge(z_state_t, y_state_t, observation=(event_t, t_min, t_max, l_attr, r_attr))

                if y_state_t not in y_stack:
                    y_stack.append(y_state_t)

            print('iter completed once!')
            print_c("[TAC2024.R2] number of states W_AIC %d" % (self.w_aic.node.__len__(),), color="green", style="bold")

        print('T-BTS constructed!')

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
            #
            # 20241210 added
            if policy_t[1].__len__() > 2:
                l_attr = policy_t[1][2]
                r_attr = policy_t[1][3]
            else:
                l_attr = 'closed'
                r_attr = 'open'             # left-closed and right-open by default
            if event_t not in policy.keys():
                policy.update({event_t : [[t_1, t_2, l_attr, r_attr]]})
            else:
                #t_list = policy[event_t]
                #t_list.append([t_1, t_2])
                #policy.update({event_t, t_list})                           # 当时为啥这么写真奇怪
                policy[event_t].append([t_1, t_2, l_attr, r_attr])          # 相同功能


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
            #
            # 20241210 added
            if policy_t[1].__len__() > 2:
                l_attr = policy_t[1][2]
                r_attr = policy_t[1][3]
            else:
                l_attr = 'closed'
                r_attr = 'open'             # left-closed and right-open by default
            if event_t not in policy_dict.keys():
                policy_dict.update({event_t : [[t_1, t_2, l_attr, r_attr]]})
            else:
                t_list = policy_dict[event_t]
                t_list.append([t_1, t_2, l_attr, r_attr])
                policy_dict.update({event_t : t_list})

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

                    if (G.edge[parent][child][0]['event'] in event_list and G.edge[parent][child][0]['event'] in event_uo) or \
                        (G.edge[parent][child][0]['event'] in event_uo and G.edge[parent][child][0]['event'] in event_uc):        # 加了这个, 而且加了后面一句, 对于所有uc都是直通的
                        if str([parent, child]) not in visited:     # 因为list本身不可哈希，所以用str(list())来代替list
                            yield parent, child                     # yield parent, child 这个版本的python没法调试yield  https://zhuanlan.zhihu.com/p/268605982
                            visited.add(str([parent, child]))       # visited.add(child)
                            if depth_now > 1:
                                stack.append((child, depth_now - 1, iter(G[child])))

                except StopIteration:
                    stack.pop()

    def dfstree(self, iwa, event_list, event_uc, event_uo, source, is_accumulate_cost=True):
        edges = list(self.dfs_edges(iwa, event_list, event_uc, event_uo, source))

        G0 = nx.MultiDiGraph()
        G0.add_node(source)

        if source == '3':
            debug_var = 27

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

            if is_accumulate_cost == True:
                try:
                    event = iwa.edge[start][end][0]['event']
                    t_min  = nx.shortest_path_length(G0, source, start, weight='t_min') + iwa.edge[start][end][0]['t_min']
                    t_max = -nx.shortest_path_length(G0, source, start, weight='t_max') + iwa.edge[start][end][0]['t_max']
                except:
                    pass
            else:
                #
                # 2024.4.20, Added
                # 这个主要是后面算NX的时候用, 不计算累计误差
                t_min = iwa.edge[start][end][0]['t_min']
                t_max = iwa.edge[start][end][0]['t_max']

            dfs_tree.add_edge(start, end, event=event, t_min=t_min, t_max=t_max)

        # 到这里计算到的都是通过uo到达的最短路径
        # 那些可经由可达时间到达的点还没有做出来
        for edge_t in edges:
            start = list(edge_t)[0]
            end   = list(edge_t)[1]

        return dfs_tree

    def dfs_edges2(self, G, event_list, event_uc, event_uo, source=None, cutoff_weight=20):
        if source is None:
            # edges for all components
            nodes = G
        else:
            # edges for components with source
            nodes = [source]
        visited = set()
        for start in nodes:
            if start in visited:
                continue
            visited.add(start)
            stack = [(start, 0, 0, iter(G[start]))]
            while stack:
                parent, t_acc_min, t_acc_max, children = stack[-1]
                try:
                    child = next(children)

                    if (G.edge[parent][child][0]['event'] in event_list and G.edge[parent][child][0]['event'] in event_uo) or \
                        (G.edge[parent][child][0]['event'] in event_uo and G.edge[parent][child][0]['event'] in event_uc):        # 加了这个, 而且加了后面一句, 对于所有uc都是直通的
                        #if str([parent, child]) not in visited:     # 因为list本身不可哈希，所以用str(list())来代替list
                        if True:                                     # 2024.5.14
                            t_min_t = G.edge[parent][child][0]['t_min']  # t_min若大于cutoff则代表完全不可达
                            t_max_t = G.edge[parent][child][0]['t_max']
                            t_acc_min += t_min_t
                            t_acc_max += t_max_t
                            #
                            # 2024.12.10 Added
                            l_attr = G.edge[parent][child][0]['l_attr']                     # 这个东西本身和iwa的边是一致的, 因此不需要递归
                            r_attr = G.edge[parent][child][0]['r_attr']

                            visited.add(str([parent, child, t_acc_min, t_acc_max]))         # visited.add(child)

                            if t_acc_min <= cutoff_weight:
                                # TODO
                                # 1 to check
                                # 2 如果算上后面的ovbservation怎么办
                                if t_acc_max > cutoff_weight:
                                    t_acc_max = cutoff_weight                               # is this way ok? 其实好像可以这么搞, 但是这个地方一定要 < 不能 <=, 因为这样可能可以在刚好t = cutoff的时候得到一个observation

                                yield parent, child, t_acc_min, t_acc_max, l_attr, r_attr   # yield parent, child 这个版本的python没法调试yield  https://zhuanlan.zhihu.com/p/268605982
                                stack.append((child, t_acc_min, t_acc_max, iter(G[child])))

                except StopIteration:
                    stack.pop()

    def all_simple_paths2(self, G0, source, target):
        path_list = list(nx.all_simple_paths(G0, source, target))
        path_list = list(set([tuple(path_list_t) for path_list_t in path_list]))

        return path_list

    def simple_shortest_longest_path_length(self, G0, source, target):
        path_list = self.all_simple_paths2(G0, source, target)              # all_simple_path很不稳定, 会让算法解出问题

        if target == '7':
            debug_var = 25

        if '7' in G0.edge.keys() and '3' in G0.edge['7'].keys():
            debug_var = 101
            if G0.edge['7']['3'].__len__() >= 10:
                debug_var = 100

        if path_list.__len__() == 0:
            return [0, 0]

        min_val = -1
        max_val = -1
        for path_t in path_list:
            min_val_t = 0
            max_val_t = 0
            for i in range(0, path_t.__len__() - 1):
                u = path_t[i]
                v = path_t[i + 1]
                min_val_t = min_val_t + G0.edge[u][v][0]['t_min']
                max_val_t = max_val_t + G0.edge[u][v][0]['t_max']
            if min_val == -1 or min_val > min_val_t and (u == v and min_val != 0):
                min_val = min_val_t
            if max_val == -1 or max_val < max_val_t:
                max_val = max_val_t

        return min_val, max_val

    def get_all_events_from_G(self, G):
        event_list_t = []
        for edge_t in G.edges(data=True):
            event_list_t.append(edge_t[2]['event'])

        event_list_t = list(set(event_list_t))
        return event_list_t

    def shortest_path_with_cost(self, G, start_node, end_node, accessible_events=None):
        # Added
        if accessible_events == None:
            accessible_events = self.get_all_events_from_G(G)

        # 用于记录从 start_node 到 end_node 的最短路径及其代价
        shortest_path = []
        min_cost = float('inf')         # 初始化最小代价为正无穷
        is_finally_accessible = []      # 表示最重算到的最小值是否可以取得, 如果是开区间则无法取得

        # 深度优先搜索递归函数，计算路径的代价
        def dfs(v, path, cost, is_accessible):
            nonlocal min_cost, shortest_path, is_finally_accessible

            # 如果当前节点是终点，则检查路径代价
            if v == end_node:
                if cost < min_cost:
                    min_cost = cost
                    shortest_path = path.copy()  # 更新最短代价路径
                    is_finally_accessible = is_accessible.copy()
                return

            # 遍历所有从 v 到邻居的边
            for neighbor in G.neighbors(v):
                for edge in G.get_edge_data(v, neighbor):  # 遍历所有从v到neighbor的边
                    edge_event = G.get_edge_data(v, neighbor, edge)['event']
                    edge_cost  = G.get_edge_data(v, neighbor, edge)['t_min']  # 获取当前边的 t_max 属性
                    if 'l_attr' in G.get_edge_data(v, neighbor, edge).keys():
                        l_attr_t = G.get_edge_data(v, neighbor, edge)['l_attr']
                    else:
                        l_attr_t = 'closed'             # left-closed by default

                    # 只遍历未在当前路径中的邻居，避免环路
                    if neighbor not in path:
                        #
                        if edge_event not in accessible_events:
                            continue

                        if l_attr_t == 'closed':
                            is_accessible_t = True
                        else:
                            is_accessible_t = False
                        #
                        path.append(neighbor)
                        is_accessible.append(is_accessible_t)                 # Added
                        dfs(neighbor, path, cost + edge_cost, is_accessible)  # 累加 t_max 作为代价
                        path.pop()  # 回溯
                        is_accessible.pop()                                   # Added

        # 从起始节点开始 DFS 搜索
        dfs(start_node, [start_node], 0, [True])

        is_min_cost_accessible = True
        for i in is_finally_accessible:
            if i == False:
                is_min_cost_accessible = False
                break

        return shortest_path, min_cost, is_min_cost_accessible

    def longest_path_with_cost(self, G, start_node, end_node, accessible_events=None):
        # Added
        if accessible_events == None:
            accessible_events = self.get_all_events_from_G(G)

        # 用于记录从 start_node 到 end_node 的所有路径及其代价
        longest_path = []
        max_cost = -float('inf')  # 初始化最大代价为负无穷
        is_finally_accessible = []  # 表示最重算到的最大值是否可以取得, 如果是开区间则无法取得

        # 记录每条路径的访问状态
        visited = set()

        # 深度优先搜索递归函数，计算路径的代价
        def dfs(v, path, cost, is_accessible):
            nonlocal max_cost, longest_path, is_finally_accessible

            # 如果当前节点是终点，则检查路径代价
            if v == end_node:
                if cost > max_cost:
                    max_cost = cost
                    longest_path = path.copy()  # 更新最长代价路径
                    is_finally_accessible = is_accessible.copy()
                return

            visited.add(v)

            for neighbor in G.neighbors(v):
                for edge in G.get_edge_data(v, neighbor):  # 遍历所有从v到neighbor的边
                    edge_event = G.get_edge_data(v, neighbor, edge)['event']
                    edge_cost = G.get_edge_data(v, neighbor, edge)['t_max']  # 获取当前边的 t_max 属性
                    if 'r_attr' in G.get_edge_data(v, neighbor, edge).keys():
                        r_attr_t = G.get_edge_data(v, neighbor, edge)['r_attr']
                    else:
                        r_attr_t = 'open'  # right-open by default
                    if neighbor not in visited:
                        #
                        if edge_event not in accessible_events:
                            continue
                        if r_attr_t == 'closed':
                            is_accessible_t = True
                        else:
                            is_accessible_t = False
                            #
                        path.append(neighbor)
                        is_accessible.append(is_accessible_t)  # Added
                        dfs(neighbor, path, cost + edge_cost, is_accessible)  # 累加 t_max 作为代价
                        path.pop()  # 回溯
                        is_accessible.pop()  # Added

            visited.remove(v)

        # 从起始节点开始 DFS 搜索
        dfs(start_node, [start_node], 0, [True])        # 自己到自己认为是可达的, 所以第一次会是True

        is_max_cost_accessible = True
        for i in is_finally_accessible:
            if i == False:
                is_max_cost_accessible = False
                break

        return longest_path, max_cost, is_max_cost_accessible

    def calulate_loop_cost(self, G0, path_t):
        min_val_t = 0
        max_val_t = 0
        for i in range(0, path_t.__len__() - 1):
            u = path_t[i]
            v = path_t[i + 1]
            min_val_t = min_val_t + G0.edge[u][v][0]['t_min']
            max_val_t = max_val_t + G0.edge[u][v][0]['t_max']

        return min_val_t, max_val_t


    def dfstree2(self, iwa, event_list, event_uc, event_uo, source, t_cutoff=20):
        edges = list(self.dfs_edges2(iwa, event_list, event_uc, event_uo, source, cutoff_weight=t_cutoff))      # [ (start, end, t_min_accumulated, t_max_accumulated, l_attr, r_attr), ... ]

        # for debugging
        if source == '3' and event_list == ['a', 'b', 'o3']:
            debug_var = 100

        #
        # Synthesize Reachibility Tree, i.e., no accumulation of transition cost
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
                    t_min  = iwa.edge[start][end][0]['t_min']
                    t_max  = iwa.edge[start][end][0]['t_max']          # 用负值，得到的最短距离就是最长距离
                    l_attr = iwa.edge[start][end][0]['l_attr']
                    r_attr = iwa.edge[start][end][0]['r_attr']
                    G0.add_edge(start, end, event=event, t_min=t_min, t_max=t_max, l_attr=l_attr, r_attr=r_attr)
            except:
                pass

        # for debugging
        # TODO to remove
        if source == '3':
            debug_var = 99

        # 2024.5.22
        # step 2 计算最小-最大值
        # step 3 求解是否存在环
        # 2024.12.10
        # 这些都不需要了, 现在accumulated value会在深度搜索时同时计算并且带出
        min_max_val = dict()
        for edge_t in edges:
            #
            u = edge_t[0]
            v = edge_t[1]
            #[min_cost_prime, max_cost_prime] = self.simple_shortest_longest_path_length(G0, source, u)      # 2024.12.7 Removed
            min_cost_prime = edge_t[2]
            max_cost_prime = edge_t[3]                                                                       # From Depth-first-search
            #min_cost_prime = min_cost_prime + G0.edge[u][v][0]['t_min']                                     # 20241213, no need
            #max_cost_prime = max_cost_prime + G0.edge[u][v][0]['t_max']

            if str(edge_t) not in min_max_val.keys():
                min_max_val[str(edge_t)] = [min_cost_prime, max_cost_prime]

        dfs_tree = nx.MultiDiGraph()
        for edge_t in edges:
            start = list(edge_t)[0]
            end   = list(edge_t)[1]

            try:
                event = iwa.edge[start][end][0]['event']
                t_min = min_max_val[str(edge_t)][0]             # identical as before, the value is calculated by shortest-path-len
                t_max = min_max_val[str(edge_t)][1]
                l_attr = G0.edge[start][end][0]['l_attr']
                r_attr = G0.edge[start][end][0]['r_attr']

                if t_min > t_cutoff:
                    t_min = t_cutoff
                    l_attr = 'closed'
                if t_max > t_cutoff:
                    t_max = t_cutoff
                    r_attr = 'open'

                if not self.is_with_edge(dfs_tree, start, end, t_min, t_max, l_attr, r_attr):
                   dfs_tree.add_edge(start, end, event=event, t_min=t_min, t_max=t_max, l_attr=l_attr, r_attr=r_attr)
            except:
                pass

        # for debugging
        if source == '3':
            if event_list == ['a', 'b', 'o3']:
                print_c("dfstree2: q0: %s, events %s / edges_obtained: %d" % (source, str(event_list), edges.__len__(),), color='bright_white', style='italic')

                try:
                    start_d = '7'
                    end_d   = '3'
                    for edge_index in dfs_tree.edge[start_d][end_d]:
                        t_min_d = dfs_tree.edge[start_d][end_d][edge_index]['t_min']
                        if t_min_d == 5.:
                            print_c("dfs_tree.edge['7'] %s" % (str(dfs_tree.edge['7'], )), color='bright_green', style='italic')
                        elif t_min_d == 6.5:
                            print_c("dfs_tree.edge['7'] %s" % (str(dfs_tree.edge['7'], )), color='bright_yellow', style='italic')

                except:
                    pass

        return dfs_tree

    def timeslice(self, dfs_tree, source):
        event_c = self.event_c
        event_o = self.event_o

        t_step = []
        t_interval = []
        for edge_t in  dfs_tree.edges():
            t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_min']
            t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][0]['t_max']
            t_step.append(t_min)
            t_step.append(t_max)

            # added, IMPORTANT
            # assign additional time instant to timeslice from controllable & observable event
            node_end = list(edge_t)[1]
            for edge_t_next in self.iwa.out_edges(node_end, data=True):
                # node_next = edge_t_next[1]
                event_t_next = edge_t_next[2]['event']
                t_min_next = edge_t_next[2]['t_min'] + t_min
                t_max_next = edge_t_next[2]['t_max'] + t_max

                if event_t_next in event_c and event_t_next in event_o:
                    t_step.append(t_min_next)
                    t_step.append(t_max_next)

        #
        # for debugging
        # DONT FORGET to check the start point for the controllable & observable event
        for edge_t_next in self.iwa.out_edges(source, data=True):
            event_t_next = edge_t_next[2]['event']
            t_min_next = edge_t_next[2]['t_min']
            t_max_next = edge_t_next[2]['t_max']

            if event_t_next in event_c and event_t_next in event_o:
                t_step.append(t_min_next)
                t_step.append(t_max_next)

        t_step = list(set(t_step))      # 排序，去除多余元素
        t_step.sort()
        for i in range(0, t_step.__len__() - 1):
            t_interval.append((t_step[i], t_step[i + 1]))
        #t_interval.sort(key=sort_timeslice)

        return t_interval

    def timeslice2(self, dfs_tree, source):
        #
        # 2024.12.10
        # 加入开区间和闭区间后, 考虑尽量减少对原策略的改动
        # 所以具体策略如下:
        #   如果半开闭或者全闭, 则仍采用左开右闭
        #   否则作为左区间时采用全开
        event_c = self.event_c
        event_o = self.event_o

        t_step      = []
        t_attr_dict = dict()            # { t_1: [is_left_closed, is_right_closed], ... }
        t_interval  = []
        for edge_t in dfs_tree.edges():
            t_min = 0
            t_max = 0
            for j in dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]].keys():
                t_min = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][j]['t_min']
                t_max = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][j]['t_max']
                t_step.append(t_min)
                t_step.append(t_max)
                #
                # 2024.12.10
                # Add区间
                l_attr = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][j]['l_attr']
                r_attr = dfs_tree.edge[list(edge_t)[0]][list(edge_t)[1]][j]['r_attr']
                #
                if t_min not in t_attr_dict.keys():
                    t_attr_dict[t_min] = [ l_attr == 'closed', False ]               # Default: left-closed and right-open
                else:
                    is_left_closed = (l_attr == 'closed') or t_attr_dict[t_min][0]
                    t_attr_dict[t_min] = [ is_left_closed, t_attr_dict[t_min][1] ]
                #
                if t_max not in t_attr_dict.keys():
                    t_attr_dict[t_max] = [ False, r_attr == 'closed' ]               # 想了一下这边左边还是开的好
                else:
                    is_right_closed = (r_attr == 'closed') or t_attr_dict[t_max][1]
                    t_attr_dict[t_max] = [ t_attr_dict[t_max][0], is_right_closed ]

            # added, IMPORTANT
            # assign additional time instant to timeslice from controllable & observable event
            node_end = list(edge_t)[1]
            for edge_t_next in self.iwa.out_edges(node_end, data=True):
                # node_next = edge_t_next[1]
                event_t_next = edge_t_next[2]['event']
                t_min_next = edge_t_next[2]['t_min'] + t_min
                t_max_next = edge_t_next[2]['t_max'] + t_max

                if event_t_next in event_c and event_t_next in event_o:
                    t_step.append(t_min_next)
                    t_step.append(t_max_next)
                    #
                    # 2024.12.10
                    # Add区间
                    l_attr = edge_t_next[2]['l_attr']
                    r_attr = edge_t_next[2]['r_attr']
                    #
                    if t_min_next not in t_attr_dict.keys():
                        t_attr_dict[t_min_next] = [ l_attr == 'closed', False ]               # Default: left-closed and right-open
                    else:
                        is_left_closed = (l_attr == 'closed') or t_attr_dict[t_min_next][0]
                        t_attr_dict[t_min_next] = [ is_left_closed, t_attr_dict[t_min_next][1] ]
                    #
                    if t_max_next not in t_attr_dict.keys():
                        t_attr_dict[t_max_next] = [ False, r_attr == 'closed' ]               # 想了一下这边左边还是开的好
                    else:
                        is_right_closed = (r_attr == 'closed') or t_attr_dict[t_max_next][1]
                        t_attr_dict[t_max_next] = [ t_attr_dict[t_max_next][0], is_right_closed ]

        #
        # for debugging
        # DONT FORGET to check the start point for the controllable & observable event
        for edge_t_next in self.iwa.out_edges(source, data=True):
            event_t_next = edge_t_next[2]['event']
            t_min_next = edge_t_next[2]['t_min']
            t_max_next = edge_t_next[2]['t_max']

            if event_t_next in event_c and event_t_next in event_o:
                t_step.append(t_min_next)
                t_step.append(t_max_next)
                #
                # 2024.12.10
                # Add区间
                l_attr = edge_t_next[2]['l_attr']
                r_attr = edge_t_next[2]['r_attr']
                #
                if t_min_next not in t_attr_dict.keys():
                    t_attr_dict[t_min_next] = [l_attr == 'closed', False]  # Default: left-closed and right-open
                else:
                    is_left_closed = (l_attr == 'closed') or t_attr_dict[t_min_next][0]
                    t_attr_dict[t_min_next] = [is_left_closed, t_attr_dict[t_min_next][1]]
                #
                if t_max_next not in t_attr_dict.keys():
                    t_attr_dict[t_max_next] = [False, r_attr == 'closed']  # 想了一下这边左边还是开的好
                else:
                    is_right_closed = (r_attr == 'closed') or t_attr_dict[t_max_next][1]
                    t_attr_dict[t_max_next] = [t_attr_dict[t_max_next][0], is_right_closed]

        t_step = list(set(t_step))      # 排序，去除多余元素
        t_step.sort()
        for i in range(0, t_step.__len__() - 1):
            if t_attr_dict[t_step[i]][0] or t_attr_dict[t_step[i]][1]:
                left_attr_t = 'closed'
            else:
                left_attr_t = 'open'

            t_interval.append((t_step[i], t_step[i + 1], left_attr_t, 'open'))       # 这里为了方便只检查左区间, 为了减少修改
        #t_interval.sort(key=sort_timeslice)

        # for debugging
        if source == '3':
            len_t = t_interval.__len__()
            if len_t == 9:
                print_c(t_interval.__len__(), color='green')
            if len_t == 8:
                print_c(t_interval.__len__(), color='bright_magenta')

        return t_interval

    def get_min_max_time_from_dfstree(self, B, source):
        # additional
        # get all minimal-maximal time for the events in a DfsTree
        event_c = self.event_c
        event_o = self.event_o

        sc_t_min = {}
        sc_t_max = {}
        for node_start in B.edge:
            for node_end in B.edge[node_start]:
                # check edgess in DfsTree
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

                # IMPORTANT
                # ADDED: checked edge for controllable & observable successive edges which is NOT LISTED in DfsTree
                for edge_t_next in self.iwa.out_edges(node_end, data=True):
                    #node_next = edge_t_next[1]
                    event_t_next = edge_t_next[2]['event']
                    t_min_next   = edge_t_next[2]['t_min'] + t_min
                    t_max_next   = edge_t_next[2]['t_max'] + t_max

                    if event_t_next in event_c and event_t_next in event_o:
                        if event_t_next not in sc_t_min.keys():
                            sc_t_min.update({event_t_next: t_min_next})
                            sc_t_max.update({event_t_next: t_max_next})
                        else:
                            if sc_t_min[event_t_next] > t_min_next:
                                sc_t_min[event_t_next] = t_min_next
                            if sc_t_max[event_t_next] < t_max_next:
                                sc_t_max[event_t_next] = t_max_next

        # for debugging
        # check the source for controllable & observable successive edges which is NOT LISTED in DfsTree
        for edge_t_next in self.iwa.out_edges(source, data=True):
            event_t_next = edge_t_next[2]['event']
            t_min_next   = edge_t_next[2]['t_min']
            t_max_next   = edge_t_next[2]['t_max']

            if event_t_next in event_c and event_t_next in event_o:
                if event_t_next not in sc_t_min.keys():
                    sc_t_min.update({event_t_next: t_min_next})
                    sc_t_max.update({event_t_next: t_max_next})
                else:
                    if sc_t_min[event_t_next] > t_min_next:
                        sc_t_min[event_t_next] = t_min_next
                    if sc_t_max[event_t_next] < t_max_next:
                        sc_t_max[event_t_next] = t_max_next


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


                t_numeraical_list = [ (elem[0], elem[1],) for elem in t_interval_list  ]
                t_lattr_list = [elem[2] == 'open'  for elem in t_interval_list ]
                t_rattr_list = [elem[3] == 'open' for elem in t_interval_list ]

                t_interval_conjuncted = intervals.union_of_half_open_intervals(t_numeraical_list, t_lattr_list, t_rattr_list)
                for i in range(0, t_interval_conjuncted.__len__()):
                    interval_t = list(t_interval_conjuncted[i])
                    if interval_t[2]:               # Bool -> str
                        interval_t[2] = 'open'
                    else:
                        interval_t[2] = 'closed'
                    if interval_t[3]:
                        interval_t[3] = 'open'
                    else:
                        interval_t[3] = 'closed'
                    t_interval_conjuncted[i] = interval_t.copy()

                # older version
                # t_interval_conjuncted = []
                # t_interval_conjuncted.append(t_interval_list.pop())
                # while t_interval_list.__len__():
                #     t_interval_to_merge = t_interval_list.pop()
                #     t_min_1 = t_interval_to_merge[0]
                #     t_max_1 = t_interval_to_merge[1]
                #
                #     for index in range(0, t_interval_conjuncted.__len__()):
                #         t_interval_prime = t_interval_conjuncted[index]
                #         t_min_2 = t_interval_prime[0]
                #         t_max_2 = t_interval_prime[1]
                #
                #         # if the time interval is intersected
                #         '''
                #             |--    |    --  --    |    --  --    |    --|
                #                 t_min_1 --.... t_min_2 ....-- t_max_1
                #
                #             |--    |    --  --    |    --  --    |    --|
                #                 t_min_2 --.... t_min_1 ....-- t_max_2
                #
                #         '''
                #         if (t_min_1 <= t_min_2 and t_min_2 <= t_max_1) or \
                #            (t_min_2 <= t_min_1 and t_min_1 <= t_max_2):
                #             t_interval_conjuncted[index][0] = min(t_min_1, t_min_2)
                #             t_interval_conjuncted[index][1] = max(t_max_1, t_max_2)
                #         else:
                #             t_interval_conjuncted.append([t_min_1, t_max_1])

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
                l_attr = t_interval[2]
                r_attr = t_interval[3]
                policy.append((event_t, (t_min, t_max, l_attr, r_attr)))

        # 2024.12.7 Added
        policy_combined = tuple(set(list(policy)))              # to remove repeated items
        # for debugging
        # if policy_combined.__len__() < policy.__len__():
        #     print_c("policy combined", color='yellow')

        return tuple(policy_combined)

    def unobservable_reach(self, current_state, policy, t_cutoff=10):
        ur_node = []
        event_t = self.get_event_from_policy(policy)

        for current_node in current_state:
            ur_node.append(current_node)

            dfs_tree = self.dfstree2(self.iwa, event_t, self.event_uc, self.event_uo, current_node, t_cutoff=t_cutoff)
            if dfs_tree.node.__len__():
                reachable_edge = list(self.dfs_ur(dfs_tree, policy, self.event_uc, self.event_uo, source=current_node))

                # for debugging
                # 不知道这个放在这里干嘛
                # [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree2(dfs_tree)

                for edge_t in reachable_edge:
                    event_c_t = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['event']
                    event_t_min = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_min']
                    event_t_max = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['t_max']
                    l_attr_t    = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['l_attr']
                    r_attr_t    = dfs_tree.edge[edge_t[0]][edge_t[1]][0]['r_attr']

                    is_control_policy_matched = False
                    for policy_t in policy:                                 # event_t_min >= policy_t[1][0]
                        #
                        if policy_t[1].__len__() > 2:
                            l_attr_tc = list(policy_t)[1][2]
                            r_attr_tc = list(policy_t)[1][3]
                        else:
                            # TODO, 检查有没有进来的
                            l_attr_tc = 'closed'
                            r_attr_tc = 'open'
                        #
                        # 2024.12.10
                        # Older vision
                        # if event_c_t in self.event_uo and \
                        #    ((event_c_t == policy_t[0] and not self.is_interval_disjoint(event_t_min, event_t_max, policy_t[1][0], policy_t[1][1])) or \
                        #     (event_c_t in self.event_uc and event_c_t in self.event_uo)):
                        #     is_control_policy_matched = True
                        #
                        # New version
                        is_intersected, intersected_interval = intervals.check_intersection_with_list((event_t_min, event_t_max, l_attr_t == 'open', r_attr_t == 'open'), [(policy_t[1][0], policy_t[1][1], l_attr_tc == 'open', r_attr_tc == 'open')])        # 注意这里的True和False和之前想法, is_open为True
                        if event_c_t in self.event_uo and \
                           ((event_c_t == policy_t[0] and is_intersected != -1) or \
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
                        #
                        t_min_t  = dfs_tree.edge[parent][child][0]['t_min']
                        t_max_t  = dfs_tree.edge[parent][child][0]['t_max']
                        if 'l_attr' in dfs_tree.edge[parent][child][0].keys():
                            l_attr_t = dfs_tree.edge[parent][child][0]['l_attr']
                        else:
                            # TODO, 检查还有没有进来的
                            l_attr_t = 'closed'                                     # left closed and right open by default
                        if 'r_attr' in dfs_tree.edge[parent][child][0].keys():
                            r_attr_t = dfs_tree.edge[parent][child][0]['r_attr']
                        else:
                            # TODO, 检查还有没有进来的
                            r_attr_t = 'open'
                        #
                        t_min_tc   = list(sc_t)[1][0]                           # tc is for input control policy
                        # t_max_tc = list(sc_t)[1][0]                           # On purpose, perhaps some issues with the older version code
                        t_max_tc   = list(sc_t)[1][1]
                        if sc_t.__len__() > 2:
                            l_attr_tc = list(sc_t)[1][2]
                            r_attr_tc = list(sc_t)[1][3]
                        else:
                            # TODO, 检查有没有进来的
                            l_attr_tc = 'closed'
                            r_attr_tc = 'open'
                        #
                        # 2024.12.10
                        # Old version
                        # if ((event_t == event_c_t and t_min_t <= t_min_tc and  self.is_interval_disjoint(t_min_t, t_max_t, t_min_tc, t_max_tc)) or        # not disjoint ?
                        #     (event_c_t in event_uc and event_c_t in event_uo)):
                        #     is_edge_reachable = True
                        #     break
                        # new version
                        is_intersected, intersected_interval = intervals.check_intersection_with_list((t_min_tc, t_max_tc, l_attr_tc == 'open', r_attr_tc == 'open'), [(t_min_t, t_max_t, l_attr_t == 'open', r_attr_t == 'open')])        # 注意这里的True和False和之前想法, is_open为True
                        if ((event_t == event_c_t and is_intersected != -1) or
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

    def observable_reach_star(self, z_state, current_y_state, t_cutoff=20):
        if self.state_type(z_state) != 'Z_state' or self.state_type(current_y_state) != 'Y_state':
            raise AssertionError('Must input correct state type')

        # for debugging
        if z_state == (('3', '5', '7'), (('a', (4, 7)),)):
            debug_var = 7

        if z_state == (('1', '2'), (('a', (1, 2)), ('o3', (3, 5.5)))):
            debug_var = 8

        #
        # 什么时候需要拆分状态?
        # e.g,
        #   o_1, [2,3)  --> 2
        #   o_1, [3,5)  --> 2, 3
        #   o_1, [5,6)  --> 3
        # 可以很简单地发现, 状态不同的时候才需要去拆
        #
        # 对于Z->Y, 考虑min-max即可, 因为要考虑Z状态中每一个点是否可以到达Y状态

        state_ur        = z_state[0]
        policy          = z_state[1]
        event_in_policy = self.get_event_from_policy(policy)

        # Step 1
        # dict for min-max time from current_y_states to nodes in z_state
        '''
        data structure:
            [ (iwa_state_1, t_min_1)),
              (iwa_state_2, t_min_2)), 
              ...
             ]
        '''

        #
        # for debugging
        if z_state == (('3', '5', '6', '7'), (('a', (2.5, 7)), ('b', (4, 7)))):
            debug_var = 11

        # observable reach with policies
        '''
        # Data structure
        #
        #   可达状态:    可观事件   初始状态1: min_cost, 区间状态; 初始状态2: min_cost, 区间状态;
        # {
        #   '7': {      o_1 : { 3 : { 1, 'closed' }, 5 : { 3, 'open' } }}
        # }

        '''
        min_time_dict, max_time_dict = self.find_min_max_time_for_Z_state(z_state, current_y_state, t_cutoff=t_cutoff)
        min_time_dict, max_time_dict = self.remove_min_max_dict_w_issues(min_time_dict, max_time_dict)                      # 去掉不存在路径的初态-末态对的信息

        '''
            Data structure
            {event_t : [(edge_end, (event_t_min, event_t_max, l_attr, r_attr))]}
        '''
        nx_star_un_merged = {}

        for tgt_node_nx in min_time_dict.keys():            # the keys of min_time_dict / max-time_dict must be identical to STATE_UR

            # event_t <- event correspond to the out edge of current node
            # 1 event_t MUST be observable
            # 2 event_t is uncontrollable
            #   event_t is controllable && event_t is picked in policy && the enabling time must identical to the observation time
            for event_t in min_time_dict[tgt_node_nx].keys():
                #
                # for min max value
                #
                for src_node_nx in min_time_dict[tgt_node_nx][event_t].keys():      # 注意这个地方src_node_nx取出的是source_state, 相当于再算了一遍
                    #
                    t_min_t = min_time_dict[tgt_node_nx][event_t][src_node_nx][0]           # src_node_nx对应初态
                    t_max_t = max_time_dict[tgt_node_nx][event_t][src_node_nx][0]           # tgt_node_nx对应末态
                    t_min_attr_t = min_time_dict[tgt_node_nx][event_t][src_node_nx][1]      # src和tgt不一定相邻但是一定可达, 不可达的前面删过一遍了
                    t_max_attr_t = max_time_dict[tgt_node_nx][event_t][src_node_nx][1]
                    #
                    # calculate reachability
                    is_reachable = False
                    #
                    # case 1
                    # 从URTree判断可达性
                    dfs_tree = self.dfstree2(self.iwa, event_in_policy, self.event_uc, self.event_uo, src_node_nx, t_cutoff=t_cutoff)              # 注意scr_node_nx是source state, 不是min_time_dict.keys(), 用的是笨办法3
                    if dfs_tree.node.__len__():
                        # if the dfs_tree can be obtained
                        reachable_edge = list(self.dfs_ur(dfs_tree, policy, self.event_uc, self.event_uo, source=src_node_nx))
                        #
                        state_rt_list = []
                        for edge_t in reachable_edge:
                            state_rt_list.append(edge_t[0])
                            state_rt_list.append(edge_t[1])
                        state_rt_list = list(set(state_rt_list))                      # 提取所有可达状态

                        for edge_rt in self.iwa.in_edges(tgt_node_nx):                # 通过URTree的可达状态可以到达目标点
                            for state_rt in state_rt_list:
                                if state_rt == edge_rt[0]:
                                    is_reachable = True
                                    l_attr_original = t_min_attr_t                    # 如果不相邻, 则取值由dfs计算
                                    r_attr_original = t_max_attr_t
                    #
                    # case 2
                    # 如果当前状态和目标状态相邻
                    for edge_rt in self.iwa.in_edges(tgt_node_nx):
                        if src_node_nx == edge_rt[0]:
                            is_reachable = True
                            l_attr_original = self.iwa.edge[src_node_nx][tgt_node_nx][0]['l_attr']      # 如果相邻, 则取值直接获得
                            r_attr_original = self.iwa.edge[src_node_nx][tgt_node_nx][0]['r_attr']
                    #
                    # for reachable states
                    # uncontrollable & observable
                    if is_reachable:
                        if event_t in self.event_o and event_t in self.event_uc:
                            #
                            # event_t_min = event_t_min + min_time_dict[state_t]  # min_time_dict[edge_start]
                            # event_t_max = event_t_max + max_time_dict[state_t]  # min_time_dict[edge_start]
                            event_t_min = t_min_t
                            event_t_max = t_max_t
                            if l_attr_original == 'closed' or t_min_attr_t == 'closed':
                                l_attr_p = 'closed'
                            else:
                                l_attr_p = 'open'
                            if r_attr_original == 'closed' or t_max_attr_t == 'closed':
                                r_attr_p = 'closed'
                            else:
                               r_attr_p = 'open'

                            if event_t not in nx_star_un_merged.keys():
                                nx_star_un_merged.update({event_t : [(tgt_node_nx, (event_t_min, event_t_max, l_attr_p, r_attr_p))]})
                                #pass
                            else:
                                nx_star_un_merged[event_t].append((tgt_node_nx, (event_t_min, event_t_max, l_attr_p, r_attr_p)))
                                #pass

                        #
                        # controllable & ovservable
                        elif event_t in self.event_o and event_t in self.event_c and event_t in event_in_policy:
                            enabled_t_min = self.get_policy_w_time(z_state)[event_t][0][0]
                            enabled_t_max = self.get_policy_w_time(z_state)[event_t][0][1]
                            enabled_l_attr = self.get_policy_w_time(z_state)[event_t][0][2]
                            enabled_r_attr = self.get_policy_w_time(z_state)[event_t][0][3]


                            # event_t_min = event_t_min + min_time_dict[state_t]              # min_time_dict[edge_start]
                            # event_t_max = event_t_max + max_time_dict[state_t]              # min_time_dict[edge_start]
                            event_t_min = t_min_t
                            event_t_max = t_max_t

                            #
                            if event_t_min <= enabled_t_min and event_t_max >= enabled_t_max:
                                event_t_min = max(event_t_min, enabled_t_min)
                                event_t_max = min(event_t_max, enabled_t_max)
                                if l_attr_original == 'closed' or t_min_attr_t == 'closed' and enabled_l_attr == 'closed':
                                    l_attr_p = 'closed'
                                else:
                                    l_attr_p = 'open'
                                if r_attr_original == 'closed' or t_max_attr_t == 'closed' and enabled_r_attr == 'closed':
                                    r_attr_p = 'closed'
                                else:
                                    r_attr_p = 'open'

                                if event_t not in nx_star_un_merged.keys():
                                    nx_star_un_merged.update({event_t: [(tgt_node_nx, (event_t_min, event_t_max, l_attr_p, r_attr_p))]})
                                else:
                                    if (tgt_node_nx, (event_t_min, event_t_max)) not in nx_star_un_merged[event_t]:
                                        nx_star_un_merged[event_t].append((tgt_node_nx, (event_t_min, event_t_max, l_attr_p, r_attr_p)))


        if nx_star_un_merged == {'o3': [('7', (3, 5.5)), ('3', (3, 5.5))]}:
            debug_var = 15

        '''
            nx_star: Data structure: 
            [ ((state_1, state_2, ...), (event_t_1, t_1, t_2, 'closed', 'open')),
              ((state_3, ),             (event_t_2, t_3, t_4, 'closed', 'open')),  
              ...
             ]

        '''
        nx_star = self.setprate_nx_star(nx_star_un_merged)

        nx_star = self.constraint_observtion_w_cutoff(nx_star, t_cutoff)


        if nx_star == [(('4',), ('o2', (3, 4))), (('4',), ('o2', (4.5, 14))), (('3',), ('o1', (1, 13.25)))]:
            debug_var = 16

        return nx_star

    def setprate_nx_star(self, nx_star_un_merged):

        # if an event can be observed through 2 OR MORE EDGES?
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

        if nx_star_un_merged == {'o3': [('7', (3, 5.5)), ('3', (3, 5.5))]}:
            debug_var = 18

        # 2024.4.20
        # Added
        # Merge first
        # 数据结构不对, 得倒一下
        #   可达状态  观测    区间
        # [ '3' : {o_1 : [(1, 2), (2, 3)]}, {o_1 : [(1, 2), (2, 3)]}, ]
        interval_list = {}
        for event_t in nx_star_un_merged.keys():
            current_interval_list = nx_star_un_merged[event_t]
            for observation_t in current_interval_list:
                reachable_state = observation_t[0]
                t_min = observation_t[1][0]
                t_max = observation_t[1][1]
                l_attr = observation_t[1][2]
                r_attr = observation_t[1][3]

                if reachable_state not in interval_list.keys():
                    interval_list.update({reachable_state : dict()})
                #
                if event_t not in interval_list[reachable_state].keys():
                    interval_list[reachable_state].update({ event_t: [(t_min, t_max, l_attr, r_attr )]})
                else:
                    interval_list[reachable_state][event_t].append((t_min, t_max, l_attr, r_attr ))

        #
        # 合并状态
        for reachable_state in interval_list:
            for event_t in interval_list[reachable_state].keys():
                #
                interval_list_t = interval_list[reachable_state][event_t]
                #
                # old version
                #interval_list_merged = self.merge_intervals(interval_list_t)
                # 20241210
                # new version
                t_numeraical_list = [ (elem[0], elem[1],) for elem in interval_list_t  ]
                t_lattr_list = [elem[2] == 'open'  for elem in interval_list_t ]
                t_rattr_list = [elem[3] == 'open' for elem in interval_list_t ]
                #
                interval_list_merged = intervals.union_of_half_open_intervals(t_numeraical_list, t_lattr_list, t_rattr_list)
                for i in range(0, interval_list_merged.__len__()):
                    interval_t = list(interval_list_merged[i])
                    if interval_t[2]:
                        interval_t[2] = 'open'
                    else:
                        interval_t[2] = 'closed'
                    if interval_t[3]:
                        interval_t[3] = 'open'
                    else:
                        interval_t[3] = 'closed'
                    interval_list_merged[i] = interval_t
                #
                interval_list[reachable_state][event_t] = interval_list_merged

        #
        # step 2
        if interval_list.__len__() == 1:
            #
            # 只有一个可达状态, 那么里面肯定都是分好的, 因为能合并的都合并了
            # 即使有多个可观事件, 那么看到的都是它
            for reachable_state in interval_list.keys():
                for event_t in interval_list[reachable_state].keys():
                    for interval_t in interval_list[reachable_state][event_t]:
                        t_min = interval_t[0]
                        t_max = interval_t[1]
                        l_attr = interval_t[2]
                        r_attr = interval_t[3]

                        nx_star.append((tuple(reachable_state), (event_t, (t_min, t_max, l_attr, r_attr))))
        else:
            if nx_star_un_merged == {'o3': [('7', (3, 5.5)), ('3', (3, 5.5))]}:
                debug_var = 19

            #
            # [
            #   [state, observation, t_min, t_max]
            #   ]
            interval_visited = []                           # 存放计算过的状态
            for reachable_state in interval_list.keys():
                for event_t in interval_list[reachable_state].keys():
                    for interval_t in interval_list[reachable_state][event_t]:
                        #
                        t_min = interval_t[0]
                        t_max = interval_t[1]
                        l_attr = interval_t[2]
                        r_attr = interval_t[3]
                        #
                        if [reachable_state, event_t, t_min, t_max, l_attr, r_attr] in interval_visited:
                            continue
                        interval_visited.append([reachable_state, event_t, t_min, t_max, l_attr, r_attr])

                        # 存放所有有交集的状态
                        # 数据结构
                        # [
                        #   [state, t_min, t_max]
                        #   ]
                        interval_to_merge = []
                        interval_to_merge.append([reachable_state, t_min, t_max, l_attr, r_attr])

                        # find possible intervals which intersects with the original interval
                        for reachable_state_prime in interval_list.keys():
                            if reachable_state == reachable_state_prime:
                                continue                                                # 目标状态不同
                            if event_t not in interval_list[reachable_state_prime].keys():
                                continue                                                # 观测相同
                            for interval_t_prime in interval_list[reachable_state_prime][event_t]:
                                t_min_prime = interval_t[0]
                                t_max_prime = interval_t[1]
                                l_attr_prime = interval_t[2]
                                r_attr_prime = interval_t[3]

                                is_intersected, intersected_interval = intervals.check_intersection_with_list(
                                    (t_min,      t_max,       l_attr == 'open',       r_attr == 'open'),
                                    [(t_min_prime, t_max_prime, l_attr_prime == 'open', r_attr_prime == 'open')])
                                is_connected = intervals.is_connected(
                                    (t_min,          t_max,       l_attr == 'open',       r_attr == 'open'),
                                    (t_min_prime,    t_max_prime, l_attr_prime == 'open', r_attr_prime == 'open'))

                                #if not self.is_interval_disjoint(t_min, t_max, t_min_prime, t_max_prime):
                                if (is_intersected != -1 or is_connected):
                                    #
                                    # 20241211
                                    # 如果两个状态有相交或者相邻
                                    if [reachable_state_prime, event_t, t_min_prime, t_max_prime] not in interval_visited:
                                        # 且没有被计算过
                                        #
                                        # 加入待计算
                                        to_merge_new = [reachable_state_prime, t_min_prime, t_max_prime, l_attr_prime, r_attr_prime]
                                        interval_to_merge.append(to_merge_new)
                                        #
                                        # 已阅
                                        interval_visited.append(to_merge_new)

                        # 合并状态
                        # 这里可以用timeslice的做法
                        # 根据上方的条件, 只要进来的区间全是相交的
                        timeslice_nx = []
                        timeslice_attr_nx = dict()
                        for event_interval_t in interval_to_merge:
                            t_min_ts = event_interval_t[1]
                            t_max_ts = event_interval_t[2]
                            l_attr_ts = event_interval_t[3]
                            r_attr_ts = event_interval_t[4]
                            if t_min_ts not in timeslice_nx:
                                timeslice_nx.append(t_min_ts)
                            if t_max_ts not in timeslice_nx:
                                timeslice_nx.append(t_max_ts)
                            #
                            if t_min_ts not in timeslice_attr_nx.keys():
                                timeslice_attr_nx[t_min_ts] = [l_attr_ts == 'closed', False]  # Default: left-closed and right-open
                            else:
                                is_left_closed = (l_attr_ts == 'closed') or timeslice_attr_nx[t_min_ts][0]
                                timeslice_attr_nx[t_min_ts] = [is_left_closed, timeslice_attr_nx[t_min_ts][1]]
                            #
                            if t_max_ts not in timeslice_attr_nx.keys():
                                timeslice_attr_nx[t_max_ts] = [False, r_attr_ts == 'closed']  # 想了一下这边左边还是开的好
                            else:
                                is_right_closed = (r_attr_ts == 'closed') or timeslice_attr_nx[t_max_ts][1]
                                timeslice_attr_nx[t_max_ts] = [timeslice_attr_nx[t_max_ts][0], is_right_closed]

                        timeslice_nx = list(set(timeslice_nx))              # 去除多余元素
                        timeslice_nx.sort()                                 # 排序
                        # 重组区间
                        interval_new_nx = []
                        for i in range(1, timeslice_nx.__len__()):
                            t_min_ts = timeslice_nx[i - 1]
                            t_max_ts = timeslice_nx[i]
                            l_attr_ts = 'closed' if timeslice_attr_nx[t_min_ts][0] else 'open'
                            r_attr_ts = 'closed' if timeslice_attr_nx[t_max_ts][1] else 'open'
                            interval_new_nx.append((t_min_ts, t_max_ts, l_attr_ts, r_attr_ts, ))
                        #
                        # 计算可达性
                        for interval_new_t in interval_new_nx:
                            t_min_ts = interval_new_t[0]
                            t_max_ts = interval_new_t[1]
                            l_attr_ts = interval_new_t[2]
                            r_attr_ts = interval_new_t[3]
                            state_list_ts = []
                            for event_interval_t in interval_to_merge:
                                state_t   = event_interval_t[0]
                                t_min_old = event_interval_t[1]
                                t_max_old = event_interval_t[2]
                                l_attr_old = event_interval_t[3]
                                r_attr_old = event_interval_t[4]

                                is_new_being_subset = intervals.is_subset([t_min_ts, t_max_ts, l_attr_ts == 'open', r_attr_ts == 'open'], [t_min_old, t_max_old, l_attr_old == 'open', r_attr_old == 'open'])
                                # if t_min_ts >= t_min_old and t_max_ts <= t_max_old:
                                if is_new_being_subset:
                                    state_list_ts.append(state_t)

                            state_list_ts = list(set(state_list_ts))    # 去除多余元素
                            state_list_ts.sort()                        # 排序
                            nx_star.append((tuple(state_list_ts), (event_t, (t_min_ts, t_max_ts, l_attr_ts, r_attr_ts))))

                            if nx_star.__len__() > 1:
                                debug_var = 21

        return nx_star

    def merge_intervals(self, interval_list_in):
        if interval_list_in.__len__() <= 1:
            return interval_list_in
        else:
            interval_list_merged = []
            interval_list_in.sort(key=lambda x: x[0])

            for i in interval_list_in:
                # 把第一个数组元素添加到新的数组种
                if not interval_list_merged:
                    interval_list_merged.append(i)
                    continue

                # 如果有重合 就更新新的数组中的最后一个元素的最大值
                if interval_list_merged[-1][1] >= i[0]:
                    t_min = interval_list_merged[-1][0]
                    t_max_prime = max(interval_list_merged[-1][1], i[1])

                    interval_list_merged[-1] = (t_min, t_max_prime, )
                else:
                    # 如果没有重合 就直接添加到新的数组中
                    interval_list_merged.append(i)

            return interval_list_merged

    def is_state_listed(self, z_state, current_state, ur_list):
        is_state_listed = False
        is_listed_state_with_the_same_y = False
        is_all_successive_policy_ending_later = True
        is_all_successive_policy_intersected_or_connected = True

        for state_t in self.w_aic.node:

            # for debugging
            if current_state == ('3', '7'):
                if z_state == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (5.5, 6.0, 'closed', 'open')))):
                    debug_var = 3
                    # for debugging
                    if state_t == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (5.0, 5.5, 'closed', 'open')))):
                        debug_var = 301
                    if state_t == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (4, 5.0, 'closed', 'open')))):
                        debug_var = 302
                    if state_t[0] == ('3', '5', '6', '7'):
                        debug_var = 304
                elif z_state == (('3', '5', '6', '7'), (('a', (9.0, 10, 'closed', 'open')), ('b', (4, 5.0, 'closed', 'open')))):
                    debug_var = 303
            elif z_state[0] == ('3', '5', '6', '7'):
                    debug_var = 304
            if state_t == (('3', '5', '6', '7'), (('b', (5, 7.0, 'closed', 'open')), ('a', (8.5, 10, 'closed', 'open')))):
                debug_var = 303

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
                    #
                    # if nx.dijkstra_path_length(self.w_aic, current_state, state_t) >= 0:
                    #     is_listed_state_with_the_same_y = True
                    # 20241210 new method
                    y_list_4_state_t = [k for k, v in ur_list.items() if state_t in v]
                    for y_t in y_list_4_state_t:
                        if y_t == current_state:
                            is_listed_state_with_the_same_y = True
                    if is_listed_state_with_the_same_y:

                        # 6 20230606: for successive states, the ending time of control policy must not be larger
                        # 7 20241210: for successive states, the policies must be connected or intersected
                        for edge_t in self.w_aic.out_edges(state_t):
                            ending_state_t = list(edge_t[1])
                            if not self.state_type(ending_state_t) == 'Z_state':
                                continue

                            policy_prime     = self.get_policy_dict(z_state[1])
                            policy_successor = self.get_policy_dict(ending_state_t[1])

                            try:
                                for key_iter in list(policy_prime.keys()):
                                    t_suc_min = policy_successor[key_iter][0][0]
                                    t_suc_max = policy_successor[key_iter][0][1]
                                    if policy_successor[key_iter][0].__len__() > 2:
                                        t_suc_lattr = policy_successor[key_iter][0][2]
                                        t_suc_rattr = policy_successor[key_iter][0][3]
                                    else:
                                        t_suc_lattr = 'closed'
                                        t_suc_rattr = 'open'
                                    #
                                    t_p_min = policy_prime[key_iter][0][0]
                                    t_p_max = policy_prime[key_iter][0][1]
                                    if policy_prime[key_iter][0].__len__() > 2:
                                        t_p_lattr = policy_successor[key_iter][0][2]
                                        t_p_rattr = policy_successor[key_iter][0][3]
                                    else:
                                        t_p_lattr = 'closed'
                                        t_p_rattr = 'open'

                                    # condition 6
                                    # if policy_successor[key_iter][0][1] <= policy_prime[key_iter][0][1]:
                                    if t_suc_max < t_p_max:                                    # t_suc_max <= t_p_max: <= is modified to <
                                        is_all_successive_policy_ending_later = False
                                        continue

                                    # condition 7
                                    is_intersected, intersected_interval = intervals.check_intersection_with_list(
                                        (t_suc_min, t_suc_max, t_suc_lattr == 'open', t_suc_rattr == 'open'),
                                        [(t_p_min, t_p_max, t_p_lattr == 'open', t_p_rattr == 'open')])
                                    is_connected = intervals.is_connected((t_suc_min, t_suc_max, t_suc_lattr == 'open', t_suc_rattr == 'open'), (t_p_min, t_p_max, t_p_lattr == 'open', t_p_rattr == 'open'))
                                    if not (is_intersected != -1 or is_connected):
                                        is_all_successive_policy_intersected_or_connected = False
                            except:
                                print("policy error in is_state_listed ...")
                                is_all_successive_policy_ending_later = False
                                is_all_successive_policy_intersected_or_connected = False
                                break

                        break
                    else:
                        # for debugging
                        is_listed_state_with_the_same_y = False

                except nx.NetworkXNoPath as e:
                    pass

        # for debugging
        if current_state == ('3', '7'):
            pass
        elif z_state[0] == ('3', '5', '6', '7'):
            debug_var = 304

        if is_state_listed and is_listed_state_with_the_same_y and is_all_successive_policy_ending_later and is_all_successive_policy_intersected_or_connected:
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

    def find_min_max_time_for_Z_state(self, z_state, current_y_state, t_cutoff=20):

        policy          = z_state[1]
        event_in_policy = self.get_event_from_policy(policy)

        # 2024.4.20
        # Data structure
        #
        #   可达状态:    可观事件   初始状态1: min_cost; 初始状态2: min_cost;
        # {
        #   '7': {      o_1 : { 3 : { 1 }, 5 : { 3 } }}
        # }
        min_time_dict = {}
        max_time_dict = {}

        # for debugging
        if z_state == (('3', '5', '6', '7'), (('a', (2.5, 7)), ('b', (4, 7)))):
            debug_var = 9

        if z_state == (('1', '2'), (('a', (1, 2)), ('o3', (3, 5.5)))):
            debug_var = 8

        # obtain min-max time by DfsTree
        for current_node in current_y_state:

            # if not current_node in min_time_dict.keys():
            #     min_time_dict.update({current_node: 0})
            # if not current_node in max_time_dict.keys():
            #     max_time_dict.update({current_node: 0})

            edges_w_min_max_weight = list(self.dfs_edges2(self.iwa, event_in_policy, self.event_uc, self.event_uo, current_node, cutoff_weight=t_cutoff))
            dfs_tree = self.dfstree2(self.iwa, event_in_policy, self.event_uc, self.event_uo, current_node, t_cutoff=t_cutoff)

            if '7' in dfs_tree.edge.keys() and '3' in dfs_tree.edge['7'].keys():
                if dfs_tree.edge['7']['3'].__len__() >= 4:
                    debug_var = 100

                    dfs_tree_for_debugging = self.dfstree2(self.iwa, event_in_policy, self.event_uc, self.event_uo, current_node)

            if dfs_tree.node.__len__():
                reachable_edge = list(self.dfs_ur(dfs_tree, policy, self.event_uc, self.event_uo, source=current_node))

                # for debugging
                # 不知道这个放在这里干嘛
                # [sc_t_min, sc_t_max] = self.get_min_max_time_from_dfstree(dfs_tree)
                for current_node_z in z_state[0]:

                    for edge_t in reachable_edge:
                        edge_start = edge_t[0]
                        edge_end   = edge_t[1]

                        # for debugging
                        if edge_end == '7' and z_state[0].__len__() > 1:
                            debug_var = 9
                            if current_node_z == '5':
                                debug_var = 10

                        # for debugging
                        if z_state == (('3', '5', '6', '7'), (('a', (2.5, 7)), ('b', (4, 7)))):
                            if current_node_z == '7' and edge_end == '7':
                                debug_var = 14

                        min_time_dict, max_time_dict = self.calculate_min_max_accumulated_cost_for_NX(current_node_z, edge_start, dfs_tree, edges_w_min_max_weight, min_time_dict, max_time_dict)
                        min_time_dict, max_time_dict = self.calculate_min_max_accumulated_cost_for_NX(current_node_z, edge_end,   dfs_tree, edges_w_min_max_weight, min_time_dict, max_time_dict)
            else:
                # for possible observations from current state but no URTree calculated
                for current_node_z in z_state[0]:
                    min_time_dict, max_time_dict = self.calculate_min_max_accumulated_cost_for_NX(current_node_z, current_node_z, dfs_tree, edges_w_min_max_weight, min_time_dict, max_time_dict)

        return min_time_dict, max_time_dict

    def calculate_min_max_accumulated_cost_for_NX(self, current_state, state_to_calculate, dfs_tree, edge_w_time_in_dfs, min_time_dict, max_time_dict):
        # find states with successive states of observable events
        successor_edges = self.iwa.out_edges(state_to_calculate, data=True)

        if current_state == '3':
            debug_var = 102

        #
        # traverse all successors
        for edge_st in successor_edges:
            edge_st_end = edge_st[1]
            event_st_t = edge_st[2]['event']

            #
            # if successor states are observable
            if event_st_t in self.event_o:

                #
                # if successor state is not in the data structure
                if not edge_st_end in min_time_dict.keys():
                    min_time_dict.update({edge_st_end: dict()})
                if event_st_t not in min_time_dict[edge_st_end].keys():
                    min_time_dict[edge_st_end].update({event_st_t: dict()})
                #
                if current_state not in min_time_dict[edge_st_end][event_st_t].keys():
                    min_time_dict[edge_st_end][event_st_t].update({current_state: [1e6, 'open']})

                if not edge_st_end in max_time_dict.keys():
                    max_time_dict.update({edge_st_end: dict()})
                #
                if event_st_t not in max_time_dict[edge_st_end].keys():
                    max_time_dict[edge_st_end].update({event_st_t: dict()})
                #
                if current_state not in max_time_dict[edge_st_end][event_st_t].keys():
                    max_time_dict[edge_st_end][event_st_t].update({current_state: [-1, 'open']})


                # update t_min and t_max
                if not dfs_tree.node.__len__():                                                                 # 其实和dfs_tree是一个东西
                    if current_state == state_to_calculate:
                        t_min_t = edge_st[2]['t_min']                                                                    # 打个补丁
                        t_max_t = edge_st[2]['t_max']
                        if edge_st[2].__len__() > 2:
                            l_attr_t = edge_st[2]['l_attr']
                            r_attr_t = edge_st[2]['r_attr']
                        else:
                            # TODO
                            l_attr_t = 'closed'
                            r_attr_t = 'open'
                    else:
                        continue
                else:
                    # 其实这边用dfs_tree的值来算累计误差其实是不科学的
                    # 这边干脆直接算完, 在NX_star里就不用再计算了
                    try:
                        # t_min_t =  nx.shortest_path_length(dfs_tree, current_state, state_to_calculate, weight='t_min')  # 注意这里的dfs_tree的cost是没有累加的, 所以最短路算出来的值是可以直接用的
                        # t_min_t = t_min_t + edge_st[2]['t_min']
                        # t_max_t = -nx.shortest_path_length(dfs_tree, current_state, state_to_calculate, weight='t_max')  # 同时为了方便计算, 这里的t_max取了负值
                        # t_max_t = t_max_t + edge_st[2]['t_max']                                                          # 其实是可以不用这么做的, 用原版的dfs_tree也能算, 但是这样好理解一些
                        #
                        # 2024.5
                        # 这里为什么要用没有累加的dfs_tree (也就是dfs_tree)?
                        # 因为这里既需要旧的可达范围, 有需要通过累计计算来获取最长距离, 所以不能用已累计的数据
                        #[t_min_t, t_max_t] = self.simple_shortest_longest_path_length(dfs_tree, current_state, state_to_calculate)      # TODO to remove
                        #
                        accessible_events = self.get_all_events_from_G(dfs_tree)
                        shortest_path_t, t_min_t, is_min_cost_accessible = self.shortest_path_with_cost(self.iwa, current_state, state_to_calculate, accessible_events)       # 20241209
                        longest_path_t,  t_max_t, is_max_cost_accessible = self.longest_path_with_cost(self.iwa,  current_state, state_to_calculate, accessible_events)       # dfs method for shortest path
                        t_min_t = t_min_t + edge_st[2]['t_min']
                        t_max_t = t_max_t + edge_st[2]['t_max']
                        #
                        # 20241210
                        # 注意这里的边界策略和最短路径有关:
                        #   最短路径里一个值达不到(为'open')就是达不到
                        #   必须要全'closed'
                        if edge_st[2].__len__() > 2:
                            # TODO
                            #
                            l_attr_t = edge_st[2]['l_attr']
                            r_attr_t = edge_st[2]['r_attr']
                        else:
                            # TODO
                            l_attr_t = 'closed'
                            r_attr_t = 'open'
                        if l_attr_t == 'closed' and is_min_cost_accessible:
                            l_attr_t = 'closed'
                        else:
                            l_attr_t = 'open'
                        if r_attr_t == 'closed' and is_max_cost_accessible:
                            r_attr_t = 'closed'
                        else:
                            r_attr_t = 'open'
                    except:
                        print("[Nx Star], no current state in edge")
                        print(dfs_tree.node)
                        print(current_state)
                        print(state_to_calculate)
                        continue

                # 2024.12.11
                # 我有一个问题, 就是如果在此处产生了多个观测, 结果会怎么样?
                #   思考以后我认为没关系
                #   因为min_time_dict里是限制了初始状态和最终状态的
                #   但是初态和末态不相邻, 但可达, 因而如果出现多个观测, 则代表两条路径
                #   所以这里的目的是求min-max距离
                #   用以计算nx的观测区间
                current_min_weight = min_time_dict[edge_st_end][event_st_t][current_state][0]
                current_max_weight = max_time_dict[edge_st_end][event_st_t][current_state][0]
                current_min_attr   = min_time_dict[edge_st_end][event_st_t][current_state][1]
                current_max_attr   = max_time_dict[edge_st_end][event_st_t][current_state][1]

                # for debugging
                # if current_min_weight != 1e6 or current_max_weight != -1:
                #     debug_var = 301

                if current_min_weight > t_min_t:                                                    # min取已有的更小的
                    min_time_dict[edge_st_end][event_st_t][current_state] = [t_min_t, l_attr_t]
                elif current_min_weight == t_min_t and current_min_attr == 'open' and l_attr_t == 'closed':
                    min_time_dict[edge_st_end][event_st_t][current_state][1] = 'closed'
                if current_max_weight < t_max_t:                                                    # max取更大的
                    max_time_dict[edge_st_end][event_st_t][current_state] = [t_max_t, r_attr_t]
                elif current_max_weight == t_max_t and current_max_attr == 'open' and r_attr_t == 'closed':
                    max_time_dict[edge_st_end][event_st_t][current_state][1] = 'closed'

        return min_time_dict, max_time_dict

    def remove_min_max_dict_w_issues(self, min_time_dict, max_time_dict):

        for tgt_node_nx in min_time_dict.keys():
            state_to_pop = []
            for event_t in min_time_dict[tgt_node_nx].keys():
                for state_t in max_time_dict[tgt_node_nx][event_t].keys():
                    if min_time_dict[tgt_node_nx][event_t][state_t][0] == 1e6 and max_time_dict[tgt_node_nx][event_t][state_t][0] == -1:
                        state_to_pop.append(state_t)
                        debug_var = 14

                for state_t in state_to_pop:
                    min_time_dict[tgt_node_nx][event_t].pop(state_t)
                    max_time_dict[tgt_node_nx][event_t].pop(state_t)

        return min_time_dict, max_time_dict

    def constraint_observtion_w_cutoff(self, state_list, t_cutoff=20):
        for i in range(0, state_list.__len__()):
            state_t = state_list[i]
            if state_t[1][1][0] > t_cutoff or state_t[1][1][1] > t_cutoff:
                # 写一样的是为了减少代码重复
                # 大多数时候这个代码不会执行
                state_t = list(state_t)
                state_t[1] = list(state_t[1])
                state_t[1][1] = list(state_t[1][1])

                if state_t[1][1][0] > t_cutoff:
                    state_t[1][1][0] = t_cutoff
                    # TODO
                    l_attr = 'closed'

                if state_t[1][1][1] > t_cutoff:
                    state_t[1][1][1] = t_cutoff
                    # TODO
                    r_attr = 'open'

                state_t[1][1] = tuple(state_t[1][1])
                state_t[1] = tuple(state_t[1])
                state_t = tuple(state_t)

                #
                state_list[i] = state_t

        return state_list

    def replace_node_in_bts(self, node, node_prime):

        # for debugging
        if node == node_prime:
            return

        in_states = []
        out_states = []
        # find all in edges for current node
        for edge_start in self.w_aic.edge.keys():
            for edge_end_t in self.w_aic.edge[edge_start]:
                if edge_end_t == node:
                    in_states.append(edge_start)

        # find all out edges for current node
        for edge_end_t in self.w_aic.edge[node]:
            out_states.append(edge_end_t)

        # add new node to T-BTS
        self.w_aic.add_node(node_prime)
        # add connections for in nodes
        for node_t in in_states:
            self.w_aic.add_edge(node_t, node_prime, control=node_prime[1])          # the edge added must be Y->Z, or Z->Z for node_prime is a Z_state, then the properities MUST be CONTROL
        # add connections for out nodes
        for node_t in out_states:
            if self.state_type(node_t) == 'Y_state':
                observation_t = self.w_aic.edge[node][node_t][0]['observation']
                self.w_aic.add_edge(node_prime, node_t, observation=observation_t)
            elif self.state_type(node_t) == 'Z_state':
                self.w_aic.add_edge(node_prime, node_t, control=node_t[1])

        # finally, remove nodes
        self.w_aic.remove_node(node)

    def find_root_state_for_z_states(self, current_y_state, z_state, ur_from_this_y_state):
        # find a root node, and then add the new Z-state to T-BTS
        # the root node must satisfy
        # 1 is from the same y-state
        # 2 the set of event is no more than the new Z-state
        # 3 the time of shared state must be smaller than the new Z-state
        # 4 find all states satisfying 1 -- 3, and the first the number of event then the overall time should be maximized
        root_state = current_y_state
        root_state_candidate = []

        for state_t in self.w_aic.node:
            if self.state_type(state_t) == 'Z_state':
                try:

                    # 1 is from the same y-state
                    #if nx.dijkstra_path_length(self.w_aic, current_y_state, state_t) >= 0:                  # 这步错了（可能）, 如果current_y_state -> state_t不通, 则不属于同一y-state, 有没有更好的办法
                    if state_t in ur_from_this_y_state:
                        event_state_t = set(self.get_policy_event(state_t))
                        event_z_state = set(self.get_policy_event(z_state))

                        # 2 the set of event is no more than the new Z-state and the set of event should not be empty
                        if event_state_t.issubset(event_z_state) and not event_state_t.__len__() == 0:

                            # 3 the time of shared state must be smaller than the new Z-state
                            policy_state_t_dict = self.get_policy_w_time(state_t)
                            policy_z_state_dict = self.get_policy_w_time(z_state)
                            is_all_time_interval_smaller = True

                            for event_t in policy_state_t_dict.keys():
                                # find all minimal & maximal time in policy_state_t & policy_z_state
                                #
                                # 找到t_list_1中最大的
                                t_list_1 = policy_state_t_dict[event_t]
                                t_min_1 = t_list_1[0][0]
                                t_max_1 = t_list_1[0][1]
                                l_attr_1 = t_list_1[0][2]
                                r_attr_1 = t_list_1[0][3]
                                for t_interval in t_list_1:
                                    t_min_prime = t_interval[0]
                                    t_max_prime = t_interval[1]
                                    l_attr_prime = t_interval[2]
                                    r_attr_prime = t_interval[3]
                                    #
                                    # 20241211, Added
                                    if t_min_prime < t_min_1:
                                        t_min_1 = t_min_prime
                                        l_attr_1 = l_attr_prime
                                    elif t_min_prime == t_min_1 and l_attr_1 == 'open':
                                        l_attr_1 = l_attr_prime
                                    if t_max_prime > t_max_1:
                                        t_max_1 = t_max_prime
                                        r_attr_1 = r_attr_prime
                                    elif t_max_prime == t_max_1 and r_attr_1 == 'open':
                                        r_attr_1 = r_attr_prime

                                #
                                # 找到t_list_2中最大的
                                t_list_2 = policy_z_state_dict[event_t]
                                t_min_2 = t_list_2[0][0]
                                t_max_2 = t_list_2[0][1]
                                l_attr_2 = t_list_2[0][2]
                                r_attr_2 = t_list_2[0][3]
                                for t_interval in t_list_2:
                                    t_min_prime = t_interval[0]
                                    t_max_prime = t_interval[1]
                                    l_attr_prime = t_interval[2]
                                    r_attr_prime = t_interval[3]
                                    #
                                    # 20241211, Added
                                    if t_min_prime < t_min_2:
                                        t_min_2 = t_min_prime
                                        l_attr_2 = l_attr_prime
                                    elif t_min_prime == t_min_2 and l_attr_2 == 'open':
                                        l_attr_2 = l_attr_prime
                                    if t_max_prime > t_max_2:
                                        t_max_2 = t_max_prime
                                        r_attr_2 = r_attr_prime
                                    elif t_max_prime == t_max_2 and r_attr_2 == 'open':
                                        r_attr_2 = r_attr_prime

                                # 只要最大的最小, 那么其他的也一定最小
                                # 注意这里最后算出来的东西不一定是区间, 可能是两个区间的组合, 比如t_min_1和t_max_1来自两个区间
                                if not (t_min_1 <= t_min_2 and t_max_1 <= t_max_2):
                                    is_all_time_interval_smaller = False
                                    break
                                # Added
                                elif t_min_1 == t_min_2 and l_attr_1 == 'closed' and l_attr_2 == 'open':
                                    is_all_time_interval_smaller = False
                                    break
                                elif t_max_1 == t_max_2 and r_attr_1 == 'closed' and r_attr_2 == 'open':
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
                t_max_attr = 'open'
                for event_t in policy_state_t_dict.keys():
                    t_list = policy_state_t_dict[event_t]
                    t_max = t_list[0][1]
                    t_max_attr = t_list[0][3]
                    for t_interval in t_list:
                        t_max_prime  = t_interval[1]
                        t_max_attr_p = t_interval[3]
                        if t_max_prime > t_max:
                            t_max = t_max_prime                 # find the maximal time in all the time interval from event_t
                            t_max_attr = t_max_attr_p
                        elif t_max_prime == t_max and t_max_attr_p == 'closed' and t_max_attr == 'open':
                            t_max_attr = 'closed'
                    time_t += t_max

                #
                candidate_event_time.append([state_t, number_of_events, time_t, t_max_attr])

            candidate_event_time.sort(key=functools.cmp_to_key(sort_root_state), reverse=True)
            root_state = candidate_event_time[0][0]
        else:
            root_state = current_y_state

        return root_state

    def assign_node_colors(self, init_marker_rgb='#DC5712', y_state_rgb='#83AF9B', z_state_rgb='#FE4365'):
        values = []
        for node_t in self.w_aic.nodes():
            if node_t == ('init',):
                values.append(init_marker_rgb)
            elif self.state_type(node_t) == 'Z_state':
                values.append(z_state_rgb)
            else:
                values.append(y_state_rgb)
        return values

    def plot(self, init_marker_rgb='#DC5712', y_state_rgb='#83AF9B', z_state_rgb='#FE4365', is_show=True):
        self.w_aic.add_edge(('init',), tuple(self.init_state))
        node_color = self.assign_node_colors(init_marker_rgb, y_state_rgb, z_state_rgb)

        pos = nx.shell_layout(self.w_aic)  # nx.spectral_layout(bts) shell_layout spring_layout
        nx.draw(self.w_aic, pos=pos, with_labels=True, node_color=node_color, font_size=8.5)

        nx.draw_networkx_edge_labels(self.w_aic, pos, font_size=6.5)  # font_size=4.5

        if is_show:
            plt.show()

    def get_predecessor(self, g, node):
        predecessor_list = []
        for node_t in g.node:
            post_pre = g.edge[node_t]
            if node in post_pre:
                predecessor_list.append(node_t)

        return predecessor_list

    def is_with_edge(self, G, u, v, t_min, t_max, l_attr, r_attr):
        """
        检查图G中是否存在一条从u到v的边，并且边的属性满足t_min, t_max, l_attr, r_attr的条件。

        Parameters:
        - G: 图对象
        - u, v: 边的起点和终点
        - t_min, t_max: 边的时间范围属性
        - l_attr, r_attr: 起点和终点的状态（'closed' 或 'open'）

        Returns:
        - True: 如果图中存在满足条件的边
        - False: 否则
        """
        # 获取起点u到终点v之间的所有边
        edges = G.get_edge_data(u, v)

        if edges is None:
            return False  # 如果没有边连接 u 和 v，返回 False

        # 遍历所有边，并检查属性是否匹配
        for key, edge_data in edges.items():
            # 检查边的属性是否符合条件
            if (edge_data['t_min'] == t_min and edge_data['t_max'] == t_max and
                    edge_data['l_attr'] == l_attr and edge_data['r_attr'] == r_attr):
                return True  # 如果找到匹配的边，返回 True

        return False  # 如果没有找到匹配的边，返回 False

    def find_all_supervisor(self, is_print=True):
        supervisor_list = []
        target = []

        for node_t in self.w_aic.nodes():
            # if self.state_type(node_t) == 'Z_state':
            #    target.append(node_t)
            target.append(node_t)

        for target_t in target:
            supervisor_t = self.all_simple_paths2(self.w_aic, tuple(self.init_state), target_t)
            for supervisor_t_t in supervisor_t:
                supervisor_list.append(supervisor_t_t)

        if is_print:
            print("[Supervisior] ---")
            for supervisor_t in supervisor_list:
                for state_t in supervisor_t:
                    print(state_t)

                print(" ")

            print("total: " +  str(supervisor_list.__len__()))

        return supervisor_list

    def remove_all_revealing_states(self, is_print_state_to_remove=True):
        '''
            TODO
            1 Obtain all z states that reveals secrets:
              (X, \gamma) \in Q_z, X \subseteq X_s
            2 at least one transition is defined when it is a Y -state;
            3 all feasible observations are defined when it is a Z-state.

            Then
            1 Collect all secret-revealing Z states Z_rev
            2 Add all Z_rev to remove list
            3 for each state q in remove list
                if state_type(q) == 'Z_states'
                    check predecessor of q
                    if state_type(Pre(q)) == 'Y_states'
                        if || Post(Pre(q)) || == 1
                            add Pre(q) to remove list
                    elif state_type(Post(z)) == 'Z_states'
                        pass
                elif state_type(q) == 'Y_states'
                    for each q' Pre(q)
                        add q' in remove list
        '''
        q_rev_list = []
        for node_t in self.w_aic.nodes():
            if self.state_type(node_t) == 'Z_state':
                q_rev_num = 0
                for state_t in list(node_t[0]):
                    if self.iwa.node[state_t].__len__():
                        q_rev_num += 1
                if q_rev_num == list(node_t[0]).__len__():
                    q_rev_list.append(node_t)

        state_to_remove = []
        while q_rev_list.__len__():
            q_rev = q_rev_list.pop()
            state_to_remove.append(q_rev)

            if self.state_type(q_rev) == 'Z_state':
                pred_list = self.get_predecessor(self.w_aic, q_rev)
                for node_t in pred_list:
                    if self.state_type(node_t) == 'Y_state':
                        if self.w_aic.edge[node_t].__len__() <= 1:
                            q_rev_list.append(node_t)
                    else:
                        remaining_post_states_to_remove = 0
                        for post_t in self.w_aic.edge[node_t]:        # if the states in pre_post are ALL going to remove
                            if post_t == q_rev or post_t in q_rev_list:
                                remaining_post_states_to_remove += 1
                        if self.w_aic.edge[node_t].__len__() <= remaining_post_states_to_remove:
                            q_rev_list.append(node_t)

            else:
                pred_list = self.get_predecessor(self.w_aic, q_rev)
                for node_t in pred_list:
                    state_to_remove.append(node_t)

        for node_t in state_to_remove:
            try:
                self.w_aic.remove_node(node_t)
            except:
                pass

        if is_print_state_to_remove:
            print_c("[State to remove] ---", color="bright_red", style='bold')
            for state_t in state_to_remove:
                print_c(state_t, color='bright_white')
            print_c("total: " +  str(state_to_remove.__len__()), color="bright_green", style='bold')


    def is_interval_disjoint(self, t_min_1, t_max_1, t_min_2, t_max_2):
        if max(t_min_1, t_min_2) < min(t_max_1, t_max_2):
            return False
        else:
            return True
