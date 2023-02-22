# Created by Anushka vidanage on January 2021
#
import sys 
import sklearn
import binascii
import csv
import gzip
import hashlib
import math
import os.path
import random
import sys
import time

import bitarray
import itertools
import numpy
import numpy.linalg
import scipy.stats
import scipy.spatial.distance
import sklearn.tree
import pickle

import networkx
import networkx.drawing

import matplotlib
matplotlib.use('Agg')  # For running on adamms4 (no display)
import matplotlib.pyplot as plt

#from libs import auxiliary

def load_attack_res_file(attack_res_file_name, enc_method, col_sep_char=',', header_line_flag=False):
  
  attack_res_dict = {} # Dictionary for attack results
  
  # Check if the file name is a gzip file or a csv file
  #
  if (data_set_name.endswith('gz')):
    in_f = gzip.open(attack_res_file_name)
  else:
    in_f = open(attack_res_file_name)
  
  # Initialise the csv reader
  #
  csv_reader = csv.reader(in_f, delimiter=col_sep_char)
  
  # Read the header line if available
  #
  if (header_line_flag == True):
    header_list = csv_reader.next()

    print 'File header line:', header_list
    print '  Attributes to be used:',
    for attr_num in attr_num_list:
      print header_list[attr_num],
      attr_name_list.append(header_list[attr_num])
    print
    
  num_rec = 0
  
  for rec_val_list in csv_reader:
    
    enc_rec_id   = rec_val_list[0]
    plain_rec_id = rec_val_list[3]
    enc_val      = rec_val_list[1]
    enc_pain_val = rec_val_list[2]
    plain_val    = rec_val_list[4]
    assign_conf  = float(rec_val_list[5])
    
    rec_id_tuple = (enc_rec_id, plain_rec_id)
    
    attack_res_list = attack_res_dict.get(rec_id_tuple, [])
    attack_res_list.append((enc_val, enc_pain_val, plain_val, assign_conf))
    attack_res_dict[rec_id_tuple] = attack_res_list
    
    num_rec += 1
    
  print 'Number of records loaded: ', num_rec
  
  return attack_res_dict

#------------------------------------------------------------------------------

def calc_attr_ent_reident_res(attack_res_dict, plain_num_rec_loaded):
  
  reident_start_time = time.time()
  
  # Two dictionaries to store unique plaintext and encoded values
  #
  enc_attr_assign_dict = {} # For each unique encoded value the set of assigned 
                            # unique plaintext values is stored
  plain_attr_assign_dict = {} # For each unique plaintext value the set of assigned 
                              # unique encoded values is stored
                              
  # Two dictionaries to store unique plaintext and encoded ids
  #
  enc_id_assign_dict = {} # For each unique encoded id the set of assigned 
                          # unique plaintext ids is stored
  plain_id_assign_dict = {} # For each unique plaintext id the set of assigned 
                            # unique encoded ids is stored
                            
  enc_org_val_dict = {} # A dictionary to store original plaintext values of
                        # encoded values
  
  # Go over each assigned record id pair
  for rec_id_pair, attack_res_list in attack_res_dict.iteritems():
    
    enc_rec_id   = rec_id_pair[0]
    plain_rec_id = rec_id_pair[1]
    
    #===========================================================================
    # # Check if there are more than one assignment for the current id pair. If there are
    # # get the most confident assignment
    # #
    #  
    # if(len(attack_res_list) > 1):
    #   attack_res_list_sorted = sorted(attack_res_list, key=lambda x: x[2], reverse=True)
    #   attack_res_tuple = select_suitable_res_tuple(attack_res_list_sorted)
    #   #attack_res_tuple = attack_res_list_sorted[0]
    # else:
    #   attack_res_tuple = attack_res_list[0]
    #   
    # enc_val       = attack_res_tuple[0]
    # enc_plain_val = attack_res_tuple[1]
    # plain_val     = attack_res_tuple[2]
    # assign_conf   = attack_res_tuple[3]
    #===========================================================================
    
    # Assign plaintext ids to encoded ids
    #
    enc_assign_plain_id_set = enc_id_assign_dict.get(enc_rec_id, set())
    enc_assign_plain_id_set.add(plain_rec_id)
    enc_id_assign_dict[enc_rec_id] = enc_assign_plain_id_set
    
    # Assign encoded ids to plaintext ids
    #
    plain_assign_enc_id_set = plain_id_assign_dict.get(plain_rec_id, set())
    plain_assign_enc_id_set.add(enc_rec_id)
    plain_id_assign_dict[plain_rec_id] = plain_assign_enc_id_set
    
    # If there are more than one encoded/plaintext assignment for record id
    # pair consider all assignments for attribute reidentification, because,
    # that can happen in the match-key attack where multiple match-keys
    # are assigned to one record.
    
    for attack_res_tuple in attack_res_list:
      
      enc_val       = attack_res_tuple[0]
      enc_plain_val = attack_res_tuple[1]
      plain_val     = attack_res_tuple[2]
      assign_conf   = attack_res_tuple[3]
       
      if(enc_val in enc_org_val_dict):
        enc_plain_val_set = enc_org_val_dict[enc_val]
        enc_plain_val_set.add(enc_plain_val)
        enc_org_val_dict[enc_val] = enc_plain_val_set
      else:
        enc_org_val_dict[enc_val] = set([enc_plain_val])
        
      # Assign plaintext values to encoded values
      #
      enc_assign_plain_val_set = enc_attr_assign_dict.get(enc_val, set())
      enc_assign_plain_val_set.add(plain_val)
      enc_attr_assign_dict[enc_val] = enc_assign_plain_val_set
      
      # Assign encoded values to plaintext values
      #
      plain_assign_enc_val_set = plain_attr_assign_dict.get(plain_val, set())
      plain_assign_enc_val_set.add(enc_val)
      plain_attr_assign_dict[plain_val] = plain_assign_enc_val_set
  
  ent_reident_res_dict, ent_reident_single_res_dict = calc_reident_res(\
                                                      enc_id_assign_dict, 
                                                      plain_id_assign_dict, 
                                                      'entity')
  attr_reident_res_dict, attr_reident_single_res_dict = calc_reident_res(\
                                                        enc_attr_assign_dict, 
                                                        plain_attr_assign_dict,
                                                        'attr', enc_org_val_dict)
  
  
  # Calcualte probabilty of suspicion for each reidentified encoded id
  #
  prob_susc_res_dict = {}
  prob_susp_val_list = []
    
  for enc_id, plain_id_set in enc_id_assign_dict.items():
    
    if(enc_id in plain_id_set):
      freq_val = len(plain_id_set)
      divisor_val = 1.0 - (1.0/plain_num_rec_loaded)
      prob_susp_val = ((1.0/freq_val) - (1.0/plain_num_rec_loaded))/divisor_val
      
      prob_susp_val_list.append(prob_susp_val)
    
  
  if(len(prob_susp_val_list) > 0):
    prob_susc_res_dict['max-ps']  = max(prob_susp_val_list)
    prob_susc_res_dict['min-ps']  = min(prob_susp_val_list)
    prob_susc_res_dict['avrg-ps'] = numpy.mean(prob_susp_val_list)
    prob_susc_res_dict['med-ps']  = numpy.median(prob_susp_val_list)
    prob_susc_res_dict['makt-ps'] = prob_susp_val_list.count(1.0)
  else:
    prob_susc_res_dict['max-ps']  = 0.0
    prob_susc_res_dict['min-ps']  = 0.0
    prob_susc_res_dict['avrg-ps'] = 0.0
    prob_susc_res_dict['med-ps']  = 0.0
    prob_susc_res_dict['makt-ps'] = 0.0
    
  
  reident_time = time.time() - reident_start_time
    
  return attr_reident_res_dict, attr_reident_single_res_dict, \
         ent_reident_res_dict, ent_reident_single_res_dict, \
         prob_susc_res_dict, reident_time

#------------------------------------------------------------------------------

def select_suitable_res_tuple(attack_res_list_sorted):
  
  conf_res_dict = {}
  
  for attack_res_tuple in attack_res_list_sorted:
    
    enc_val       = attack_res_tuple[0]
    enc_plain_val = attack_res_tuple[1]
    plain_val     = attack_res_tuple[2]
    assign_conf   = attack_res_tuple[3]
    
    res_list = conf_res_dict.get(assign_conf, [])
    res_list.append((enc_val, enc_plain_val, plain_val))
    conf_res_dict[assign_conf] = res_list
  
  conf_res_dict_item_list = sorted(conf_res_dict.items(), key=lambda x: x[0], reverse=True)
  
  conf_res_list = conf_res_dict_item_list[0]
  conf_res_tuple = conf_res_dict_item_list[0]
  
  assign_conf = conf_res_tuple[0]
  conf_res_list = conf_res_tuple[1]
  
  select_flag = False
    
  for res_tuple in conf_res_list:
    enc_val       = res_tuple[0]
    enc_plain_val = res_tuple[1]
    plain_val     = res_tuple[2]
    assign_conf   = res_tuple[0]
        
    if(enc_plain_val == plain_val):
      select_flag = True
      return_res_tuple = (enc_val, enc_plain_val, plain_val, assign_conf)
      break
  
  if(select_flag == False):
    res_tuple = conf_res_list[0]
    enc_val       = res_tuple[0]
    enc_plain_val = res_tuple[1]
    plain_val     = res_tuple[2]
    return_res_tuple = (enc_val, enc_plain_val, plain_val, assign_conf)    
      
  return return_res_tuple  

#------------------------------------------------------------------------------

def calc_reident_res(enc_assign_dict, plain_assign_dict, reident_type, enc_org_val_dict=None):
  
  reident_res_dict = {}
  reident_single_res_dict = {}
  
  def get_plain_val_set(next_enc_vals):
    next_plain_val_set = set()
    next_path_set = set()
    for enc_val in next_enc_vals:
      next_plain_val_set = next_plain_val_set.union(enc_assign_dict[enc_val])
      
      for plain_val in enc_assign_dict[enc_val]:
        next_path_set.add((enc_val, plain_val))
    
    return next_plain_val_set, next_path_set
  
  def get_enc_val_set(next_plain_vals):
    next_enc_val_set = set()
    next_path_set = set()
    for plain_val in next_plain_vals:
      next_enc_val_set = next_enc_val_set.union(plain_assign_dict[plain_val])
      
      for enc_val in plain_assign_dict[plain_val]:
        next_path_set.add((enc_val, plain_val))
    
    return next_enc_val_set, next_path_set 
  
  #=============================================================================
  # match_1_1_pair_set = set()
  # match_1_m_pair_set = set()
  # match_m_1_pair_set = set()
  # match_m_m_pair_set = set()
  #=============================================================================
  
  processed_plain_val_set = set()
  processed_enc_val_set = set()
  
  #print 'starting the loop'
  
  for enc_rec_val in enc_assign_dict.keys():
    
    if(enc_rec_val in processed_enc_val_set):
      continue
    
    #print enc_rec_id
    all_paths_set = set()
    
    curr_enc_val_set = set([enc_rec_val])
    curr_plain_val_set = set()
    
    prev_enc_val_set = set()
    prev_plain_val_set = set()
    
    while (curr_enc_val_set != prev_enc_val_set):
      
      new_enc_val_set = curr_enc_val_set - prev_enc_val_set
      next_pain_val_set, next_pain_val_path_set = get_plain_val_set(new_enc_val_set)
      
      #print next_pain_val_set
      #print next_pain_val_path_set
      
      all_paths_set = all_paths_set.union(next_pain_val_path_set)
      
      assert len(processed_plain_val_set.intersection(next_pain_val_set)) == 0, \
                          (processed_plain_val_set.intersection(next_pain_val_set))
      
      prev_plain_val_set = curr_plain_val_set.copy()
      curr_plain_val_set = curr_plain_val_set.union(next_pain_val_set)
      
      if(curr_plain_val_set != prev_plain_val_set):
        new_plain_val_set = curr_plain_val_set - prev_plain_val_set
        next_enc_val_set, next_enc_val_path_set = get_enc_val_set(new_plain_val_set)
        
        #print next_enc_id_set
        #print next_enc_id_path_set
        
        assert len(processed_enc_val_set.intersection(next_enc_val_set)) == 0, \
                          (processed_enc_val_set.intersection(next_enc_val_set))
        
        all_paths_set = all_paths_set.union(next_enc_val_path_set)
        
        prev_enc_val_set = curr_enc_val_set.copy()
        curr_enc_val_set = curr_enc_val_set.union(next_enc_val_set)
      
      else:
        prev_enc_val_set = curr_enc_val_set.copy()
    
    #print 'end of one set of paths'
    
    processed_enc_val_set = processed_enc_val_set.union(curr_enc_val_set)
    processed_plain_val_set = processed_plain_val_set.union(curr_plain_val_set)
    
    #print 'processed enc ids', processed_enc_val_set
    #print 'processed plain ids', processed_plain_val_set
    #print all_paths_set
    #print
    
    match_type = ''
    
    if(len(curr_enc_val_set) == 1 and len(curr_plain_val_set) == 1):
      #match_1_1_pair_set = match_1_1_pair_set.union(all_paths_set)
      match_type = '1-1'
    elif(len(curr_enc_val_set) == 1 and len(curr_plain_val_set) > 1):
      #match_1_m_pair_set = match_1_m_pair_set.union(all_paths_set)
      match_type = '1-m'
    elif(len(curr_enc_val_set) > 1 and len(curr_plain_val_set) == 1):
      #match_m_1_pair_set = match_m_1_pair_set.union(all_paths_set)
      match_type = 'm-1'
    elif(len(curr_enc_val_set) > 1 and len(curr_plain_val_set) > 1):
      #match_m_m_pair_set = match_m_m_pair_set.union(all_paths_set)
      match_type = 'm-m'
    else:
      print '***Warning! Cannot happen...'
      print len(curr_enc_val_set), len(curr_plain_val_set)
      sys.exit()
    
    one_corr = False
    all_corr = True
    num_corr_pairs = 0
    num_wrng_pairs = 0
    single_match_type = match_type
    
    for enc_val in curr_enc_val_set:
      
      if(reident_type == 'entity'):
        if(enc_val in curr_plain_val_set):
          num_corr_pairs += 1
          one_corr = True
        else:
          num_wrng_pairs += 1
          all_corr = False
          
      elif(reident_type == 'attr'):
        enc_plain_val_set = enc_org_val_dict[enc_val]
        if(len(enc_plain_val_set.intersection(curr_plain_val_set)) > 0):
          num_corr_pairs += 1
          one_corr = True
        else:
          num_wrng_pairs += 1
          all_corr = False
    
    if(all_corr == False):
      if(one_corr):
        match_type += '-p'
      else:
        match_type += '-w'
    
    reident_res_dict[match_type] = reident_res_dict.get(match_type, 0) + 1
    reident_single_res_dict[single_match_type] = reident_single_res_dict.get(single_match_type, 0) + num_corr_pairs
    reident_single_res_dict['wrng'] = reident_single_res_dict.get('wrng', 0) + num_wrng_pairs
      
  #=============================================================================
  # reident_res_dict['1-1'] = match_1_1_pair_set
  # reident_res_dict['1-m'] = match_1_m_pair_set
  # reident_res_dict['m-1'] = match_m_1_pair_set
  # reident_res_dict['m-m'] = match_m_m_pair_set
  #=============================================================================
      
  return reident_res_dict, reident_single_res_dict
  

#===============================================================================
# Test programme
#===============================================================================

#===============================================================================
# enc_id_assign_dict = {1:set(['A', 'B', 'D']), 2:set(['A', 'D']), 3:set(['C', 'E']), 
#                       4:set(['G']), 5:set(['F']), 6:set(['G']), 7:set(['G'])}
# plain_id_assign_dict = {'A':set([1, 2]), 'B':set([1]), 'C':set([3]), 'D':set([1, 2]), 
#                         'E':set([3]), 'F':set([5]), 'G':set([4, 6, 7])}
#===============================================================================

#===============================================================================
# enc_id_assign_dict = {1:set(['A', 'B']), 2:set(['A', 'C']), 3:set(['F']), 
#                       4:set(['E', 'G']), 5:set(['D']), 6:set(['H']), 7:set(['F']),
#                       8:set(['J']), 9:set(['H', 'I']), 10:set(['F']), 11:set(['J']),
#                       12:set(['I']), 13:set(['K'])}
# plain_id_assign_dict = {'A':set([1, 2]), 'B':set([1]), 'C':set([2]), 'D':set([5]), 
#                         'E':set([4]), 'F':set([3, 7, 10]), 'G':set([4]), 'H':set([6, 9]), 
#                         'I':set([9, 12]), 'J':set([8, 11]), 'K':set([13]),}
#===============================================================================


#===============================================================================
# enc_id_assign_dict = {1:set([1, 3]), 2:set([1, 2]), 3:set([7]), 
#                       4:set([8, 4]), 5:set([5]), 6:set([6]), 7:set([7]),
#                       8:set([10]), 9:set([6, 9]), 10:set([7]), 11:set([10]),
#                       12:set([9]), 13:set([15])}
# plain_id_assign_dict = {1:set([1, 2]), 3:set([1]), 2:set([2]), 5:set([5]), 
#                         8:set([4]), 7:set([3, 7, 10]), 4:set([4]), 6:set([6, 9]), 
#                         9:set([9, 12]), 10:set([8, 11]), 15:set([13]),}
#  
# ent_reident_res_dict = calc_reident_res(enc_id_assign_dict, plain_id_assign_dict, 'entity')
#  
# for i, v in ent_reident_res_dict.iteritems():
#   print i
#   print v
#   print
#===============================================================================

