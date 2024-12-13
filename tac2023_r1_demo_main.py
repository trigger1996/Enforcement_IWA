
#!/usr/bin/python
# -*- coding:utf-8 -*-
from opacity_iwa.t_aic_4 import w_aic
from utils import print_c
import control_2_trajectory

from random import randint

event_uo = ['a',  'b',  'uc']
event_o  = ['o1', 'o2', 'o3']
event_c  = ['a',  'b',  'o3']
event_uc = ['o1', 'o2', 'uc']

def main():

    w_aic_2 = w_aic('./opacity_iwa/iwa/IWA_4.3.r1_w_urcycles.yaml', ['1'], event_c, event_o, event_uc, event_uo)

    w_aic_2.construct_W_AIC(t_cutoff=10)

    #w_aic_2.remove_all_revealing_states()

    supervisor_2 = w_aic_2.find_all_supervisor(is_print=True)

    print_c("[TAC2024.R1] number of states W_AIC %d" % (w_aic_2.w_aic.node.__len__(),), color="green", style="bold")
    #t_aic_1.plot()
    w_aic_2.plot()

if __name__ == '__main__':
    main()
    print('Finished')
