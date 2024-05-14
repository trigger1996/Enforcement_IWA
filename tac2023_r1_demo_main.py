
#!/usr/bin/python
# -*- coding:utf-8 -*-
from opacity_iwa.t_aic_4 import t_bts
import control_2_trajectory

from random import randint

event_uo = ['a',  'b',  'uc']
event_o  = ['o1', 'o2', 'o3']
event_c  = ['a',  'b',  'o3']
event_uc = ['o1', 'o2', 'uc']

def main():

    t_bts_2 = t_bts('./opacity_iwa/iwa/IWA_4.3.r1_w_urcycles.yaml', ['1'], event_c, event_o, event_uc, event_uo)

    t_bts_2.construct_T_BTS()

    #t_bts_2.remove_all_revealing_states()

    supervisor_2 = t_bts_2.find_all_supervisor(is_print=True)


    #t_aic_1.plot()
    t_bts_2.plot()

if __name__ == '__main__':
    main()
    print('Finished')
