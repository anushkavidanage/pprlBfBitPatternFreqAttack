# Bloom filter attack using a frequency set-based approach
#
# Dinusha Vatsalan, Thilina Ranbaduge, Rainer Schnell, and Peter Christen
# Sept 2016
#
# Edited on Feb 2023 by Anushka Vidanage
#
# INI, DLA programme
#
# Usage:
#   python bf_attack_bit_pattern_freq.py [q] [hash_type] [num_hash_funct] [bf_len] [bf_harden]
#                       [bf_encode] [bf_num_bits] [padded]
#                       [min_freq] [num_freq_attr_val_list]
#                       [build_data_set_name] [build_rec_id_col]
#                       [build_col_sep] [build_header_line_flag]
#                       [build_attr_list]
#                       [analysis_data_set_name] [analysis_rec_id_col]
#                       [analysis_col_sep] [analysis_header_line_flag]
#                       [analysis_attr_list]
# where:
# q                         is the length of q-grams to use
# hash_type                 is either DH (double-hashing) or RH
#                           (random hashing)
# num_hash_funct            is a positive number or 'opt' (to fill BF 50%)
# bf_len                    is the length of Bloom filters
# bf_harden                 is either None, 'balance' or 'fold' for different
#                           BF hardening techniques
# bf_encode                 is the Bloom filter encoding method
# padded                    is a flag set to True if padding is applied 
#                           and False otherwise
# min_freq                  is the minimum frequency of Bloom filters and
#                           attribute values to consider in the analysis
# num_freq_attr_val_list    is a list with the numbers of most frequent
#                           attribute values from the analysis file we aim to
#                           re-identify
#
# build_data_set_name       is the name of the CSV file to use for building the
#                           frequency analysis tables
# build_rec_id_col          is the column in the CSV file containing record
#                           identifiers
# build_col_sep             is the character to be used to separate fields in
#                           the input file
# build_header_line_flag    is a flag, set to True if the file has a header
#                           line with attribute (field) names
# build_attr_list           is the list of attributes to encode and use for the
#                           linkage
# 
# analyse_data_set_name     is the name of the CSV file to analyse
# analyse_rec_id_col        is the column in the CSV file containing record
#                           identifiers
# analyse_col_sep           is the character to be used to separate fields in
#                           the input file
# analyse_header_line_flag  is a flag, set to True if the file has a header
#                           line with attribute (field) names
# analyse_attr_list         is the list of attributes to get values from to
#                           guess if they can be re-identified
# enc_param_list            is a list of parameters that need to be defined
#                           based on encoding method (otherwise None)
#                           # if encoding method == RBF
#                             parameter list = [abf_len_type, num_bits_list]
#                             - abf_len_type   is the way to define ABF length
#                                              can be either dynamic or static
#                             - num_bits_list  is the list of percentages of 
#                                              number of bits need to be
#                                              selected from each ABF to
#                                              generate RBF
#                           # if encoding method == CLKRBF
#                             parameter list = [num_hash_funct_list]
#                             - num_hash_funct_list is a list of hash functions
#                                                   for each encoding attribute
#
# harden_param_list         is a list of parameters that need to be defined
#                           based on hardening method
#                           # if hardening method == mchain
#                             parameter list = [chain_len, sel_method]
#                             - chain_len   is the number of extra q-grams to
#                                           be added
#                             - sel_method  the method of how q-grams are being 
#                                           selected. Can either be 
#                                           probabilistic or frequency based
#                           # if hardening method == balance
#                             parameter list = [random_seed]
#                             - random_seed   set to True if random seed need
#                                             to be defined

#is the percentage of the number of bits need to be
#                           used for each attibute value specified
#
# Note that if the analysis data set is the same as the build data set (with
# the same attributes) then only one analysis (on the build data set itself)
# will be carried out.

# Example call (on laptop):
# python bf_attack-pakdd-2017.py 2 DH 1 1000 balance CLK [1.0] False 100 [10,20] <path-to-datasets>/dataset-1.csv.gz 0 , True [1] <path-to-datasets>/dataset-2.csv.gz 0 , True [1]

# -----------------------------------------------------------------------------

MAX_MEMORY_USE = 70000  # In Megabytes

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

# Standard library imports
#
import csv
import gzip
import hashlib
import os.path
import sys
import time
import bitarray
import numpy
import random

from libs import auxiliary
from libs import eval_attack_res

# PPRL module imports
#
from libs import encoding
from libs import hashing
from libs import hardening

PAD_CHAR = chr(1)   # Used for q-gram padding

BF_HASH_FUNCT1 = hashlib.sha1
BF_HASH_FUNCT2 = hashlib.md5
BF_HASH_FUNCT3 = hashlib.sha224

today_str = time.strftime("%Y%m%d", time.localtime())

# Input variable definitions
#
freq =    'freq'
prob =    'prob'
dynamic = 'dynamic'
static =  'static'

# -----------------------------------------------------------------------------

def load_data_set_extract_attr_val(file_name, rec_id_col, use_attr_list,
                                   col_sep_char, header_line):
  """Load the given file, extract all attributes and get them into a single 
     list. 

     Returns:
     1) a list of total record values.
     2) a dictionary of record values where keys are record ids and values
        are all the attribute values of that record.
     3) a dictionary of record value frequencies where keys are record
        values and values are frequencies.
     4) and a list of the attribute names used.
  """

  start_time = time.time()

  if (file_name.endswith('gz')):
    f = gzip.open(file_name)
  else:
    f = open(file_name)

  csv_reader = csv.reader(f, delimiter=col_sep_char)

  print 'Load data set from file:', file_name
  print '  Attribute separator: %c' % (col_sep_char)
  if (header_line == True):
    header_list = csv_reader.next()
    print '  Header line:', header_list

  use_attr_name_list = []

  if (header_line == True):
    print '  Record identifier attribute:', header_list[rec_id_col]
  else:
    print '  Record identifier attribute number:', rec_id_col
  if (header_line == True):
    print '  Attributes to use:',
    for attr_num in use_attr_list:
      use_attr_name = header_list[attr_num]
      print use_attr_name,
      use_attr_name_list.append(use_attr_name)
  print

  rec_num = 0
  
  # A list containing all record values
  #
  total_rec_list = []
  
  # A dictionary of encoded record values in each record
  #
  rec_val_dict = {}
  
  # A dictionary with record values as keys and record ids as values
  #
  rec_val_id_dict = {}
  
  # A dictionary of encoded record value frequencies
  #
  rec_val_freq_dict = {}
  
  # Removed and confidential records. These records do not have any
  # attribute values
  num_rec_with_removed = 0
  num_rec_with_conf = 0

  for rec_list in csv_reader:
    
    if('removed' in rec_list):
      num_rec_with_removed += 1
      continue
      
    if('confidential' in rec_list):
      num_rec_with_conf += 1
      continue
    
    
    rec_num += 1

    if (rec_num % 100000 == 0):
      time_used = time.time() - start_time
      print '  Processed %d records in %d sec (%.2f msec average)' % \
            (rec_num, time_used, 1000.0*time_used/rec_num)
      print '   ', auxiliary.get_memory_usage()

      auxiliary.check_memory_use(MAX_MEMORY_USE)
    
    # Get record ID
    rec_id = rec_list[rec_id_col].strip().lower()
    if '-' in rec_id:
      rec_id = rec_id.split('-')[1].strip()
    
    # A list of attribute values per record
    rec_val_list      = []
    
    # A list of attribute values (per record) which will be used for encoding
    use_attr_val_list = [] 
    
    # Loop over each attribute value in the record
    for (i, attr_val) in enumerate(rec_list):
      rec_val_list.append(attr_val.strip().lower())
      
      # Check if current attribute is specified to be encoded
      if(i in use_attr_list):
        use_attr_val_list.append(attr_val.strip().lower())
    
    total_rec_list.append(rec_val_list)
    
    # Join all attribute values to a single string
    rec_val = ' '.join(use_attr_val_list) 
    rec_val_dict[rec_id] = rec_val
    
    val_id_set = rec_val_id_dict.get(rec_val, set())
    val_id_set.add(rec_id)
    rec_val_id_dict[rec_val] = val_id_set
    
    rec_val_freq_dict[rec_val] = rec_val_freq_dict.get(rec_val, 0) + 1

  time_used = time.time() - start_time
  print '  Processed %d records in %d sec (%.2f msec average)' % \
        (rec_num, time_used, 1000.0*time_used/rec_num)
  print '   ', auxiliary.get_memory_usage()
  
  print
  print '  Number of dismissed records with value \'removed\':', num_rec_with_removed
  print '  Number of dismissed records with value \'confidential\':', num_rec_with_conf
  print
  
  assert len(total_rec_list) == rec_num

  return total_rec_list, rec_val_dict, rec_val_id_dict, rec_val_freq_dict, use_attr_name_list

# -----------------------------------------------------------------------------

def gen_bloom_filter_dict(rec_val_list, rec_id_col, encode_method, hash_type,
                          bf_len, num_hash_funct, use_attr_list, q, padded, 
                          bf_harden, enc_param_list=None, harden_param_list=None):
  """Using given record value list generate Bloom filters by encoding specified
     attribute values from each record using given q, bloom filter length, and
     number of hash functions.
     
     When encoding use the given encode method, hashing type, padding, and 
     hardening method.

     Return a dictionary with bit-patterns each of length of the given Bloom
     filter length.
  """

  print 'Generate Bloom filter bit-patterns for %d records' % \
        (len(rec_val_list))
  print '  Bloom filter length:          ', bf_len
  print '  q-gram length:                ', q
  print '  Number of hash functions used:', num_hash_funct
  print '  Encoding method:              ', encode_method
  print '  Hashing type used:            ', \
        {'dh':'Double hashing', 'rh':'Random hashing', 
         'edh':'Enhanced Double hashing', 'th':'Triple hashing',}[hash_type]
  print '  Padded:                       ', padded
  print '  Hardening method:             ', bf_harden

  bf_dict= {}  # One BF per record

  #bf_pos_map_dict = {}  # For each bit position the q-grams mapped to it

  bf_num_1_bit_list = []  # Keep number of bits set to calculate avrg and std

  start_time = time.time()

  rec_num = 0
  
  hash_method_list = []
  
  #-------------------------------------------------------------------------
  # Define hashing method
  #
  if(hash_type == 'dh'): # Double Hashing
    if(encode_method == 'clkrbf' and len(use_attr_list) > 1):
      dynamic_num_hash_list = enc_param_list[0]
      
      for num_hash in dynamic_num_hash_list:
        HASH_METHOD =  hashing.DoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2, 
                                         bf_len, num_hash)
        hash_method_list.append(HASH_METHOD)
    else:
      HASH_METHOD =  hashing.DoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2, 
                                         bf_len, num_hash_funct)
  elif(hash_type == 'rh'): # Random Hashing
    if(encode_method == 'clkrbf' and len(use_attr_list) > 1):
      dynamic_num_hash_list = enc_param_list[0]
      
      for num_hash in dynamic_num_hash_list:
        HASH_METHOD =  hashing.RandomHashing(BF_HASH_FUNCT1, bf_len, 
                                             num_hash)
        hash_method_list.append(HASH_METHOD)
    else:
      HASH_METHOD =  hashing.RandomHashing(BF_HASH_FUNCT1, bf_len, 
                                           num_hash_funct)
  elif(hash_type == 'edh'): # Enhanced Double Hashing
    if(encode_method == 'clkrbf' and len(use_attr_list) > 1):
      dynamic_num_hash_list = enc_param_list[0]
      
      for num_hash in dynamic_num_hash_list:
        HHASH_METHOD = hashing.EnhancedDoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                     bf_len, num_hash)
        hash_method_list.append(HASH_METHOD)
    else:
      HASH_METHOD = hashing.EnhancedDoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                  bf_len, num_hash_funct)
  else: # hash_type == 'th' # Triple Hashing
    if(encode_method == 'clkrbf' and len(use_attr_list) > 1):
      dynamic_num_hash_list = enc_param_list[0]
      
      for num_hash in dynamic_num_hash_list:
        HASH_METHOD = hashing.TripleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2, 
                                            BF_HASH_FUNCT3, bf_len, 
                                            num_hash)
        hash_method_list.append(HASH_METHOD)
    else:
      HASH_METHOD = hashing.TripleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2, 
                                          BF_HASH_FUNCT3, bf_len, 
                                          num_hash_funct)
  
  #-------------------------------------------------------------------------
  # Define encoding method
  # 
  if(encode_method == 'abf'): # Attribute-level Bloom filter
    ENC_METHOD = encoding.AttributeBFEncoding(use_attr_list[0], q, padded, 
                                              HASH_METHOD)
  elif(encode_method == 'clk'): # Cryptographic Long-term Key
    rec_tuple_list = []
    
    for att_num in use_attr_list:
      rec_tuple_list.append([att_num, q, padded, HASH_METHOD])
  
    ENC_METHOD = encoding.CryptoLongtermKeyBFEncoding(rec_tuple_list)
    
  elif(encode_method == 'rbf'): # Record-level Bloom filter
    
    abf_len_type  = enc_param_list[0] # Dymaic or Static
    num_bits_list = enc_param_list[1] # List of percentages of number of bits
    
    rec_tuple_list = []
    
    for (i, att_num) in enumerate(use_attr_list):
      rec_tuple_list.append([att_num, q, padded, HASH_METHOD, 
                             int(num_bits_list[i]*bf_len)])
    
    ENC_METHOD = encoding.RecordBFEncoding(rec_tuple_list)
    
    if(abf_len_type == 'dynamic'):
      avr_num_q_gram_dict = ENC_METHOD.get_avr_num_q_grams(rec_val_list)
      abf_len_dict = ENC_METHOD.get_dynamic_abf_len(avr_num_q_gram_dict, 
                                                    num_hash_funct)
      ENC_METHOD.set_abf_len(abf_len_dict)
 
  else: # encode_method == 'clkrbf'
    rec_tuple_list = []
    
    for (i, att_num) in enumerate(use_attr_list):
      rec_tuple_list.append([att_num, q, padded, hash_method_list[i]])
    
    ENC_METHOD = encoding.CryptoLongtermKeyBFEncoding(rec_tuple_list)
  
  #-------------------------------------------------------------------------
  # Define hardening method
  #
  if(bf_harden == 'balance'): # Bloom filter Balancing
    input_random_seed = harden_param_list[0]
    
    if(input_random_seed):
      rand_seed = random.randint(1,100)
      BFHard = hardening.Balancing(rand_seed)
    else:
      BFHard = hardening.Balancing()
    
  elif(bf_harden == 'fold'): # Bloom filter XOR Folding
    BFHard = hardening.Folding()
    
  elif(bf_harden == 'rule90'): # Bloom filter Rule 90
    BFHard = hardening.Rule90()
    
  elif(bf_harden == 'wxor'): # Bloom filter Window based XOR
    BFHard = hardening.WXOR(harden_param_list[0])
    
  elif(bf_harden == 'resample'): # Bloom filter resampling based XOR
    BFHard = hardening.RESAMPLE('samplebf76')
    
  elif(bf_harden == 'mchain'): # Bloom filter Markov Chain
    
    chain_len  = harden_param_list[0]
    sel_method = harden_param_list[1]
    
    # Get a single list of all attribute values 
    lang_model_val_list = []
    
    for rec_val in rec_val_list:
      val_list = []
      
      for attr_num in use_attr_list:
        val_list.append(rec_val[attr_num])
      
      rec_str = ' '.join(val_list)
      
      lang_model_val_list.append(rec_str)
    
    # Initialize Markov Chain class
    BFHard = hardening.MarkovChain(q, padded, chain_len, sel_method)
    
    # Calculate transition probability
    BFHard.calc_trans_prob(lang_model_val_list)
    
  #elif(bf_harden == 'salt'): # Bloom filter Salting
  #  salt_str_list = ['ax', '43', 'bf7', '#']
  
  #-------------------------------------------------------------------------
  # Loop over each record and encode relevant attribute values to a 
  # Bloom filter
  #
  for attr_val_list in rec_val_list:
    rec_num += 1

    if (rec_num % 100000 == 0):
      time_used = time.time() - start_time
      print '  Generated %d Bloom filters in %d sec (%.2f msec average)' % \
            (rec_num, time_used, 1000.0*time_used/rec_num)
      print '   ', auxiliary.get_memory_usage()

      auxiliary.check_memory_use(MAX_MEMORY_USE)
    
    # Apply Bloom filter hardening if required
    #
    rec_id = attr_val_list[rec_id_col].strip().lower() # Get record ID number
    if '-' in rec_id:
      rec_id = rec_id.split('-')[1].strip()
      
    if(bf_harden in ['balance', 'fold', 'rule90']):
      rec_bf = ENC_METHOD.encode(attr_val_list)
      rec_bf = BFHard.harden_bf(rec_bf)
      
    elif(bf_harden == 'mchain'):
      rec_bf = ENC_METHOD.encode(attr_val_list, None, BFHard)
    
    elif(bf_harden in ['wxor', 'resample']):
      rec_bf = ENC_METHOD.encode(attr_val_list)
      rec_bf = BFHard.harden_bf(rec_bf)
    
    elif(bf_harden == 'salt'):
      salt_str = attr_val_list[5] 
      if(encode_method == 'abf'):
        rec_bf = ENC_METHOD.encode(attr_val_list, salt_str)
      else:
        rec_bf = ENC_METHOD.encode(attr_val_list, 
                                   [salt_str for _ in 
                                    range(len(use_attr_list))])
        
    else: # bf_harden == 'none'
      rec_bf = ENC_METHOD.encode(attr_val_list)
        
    # Add final Bloom filter to the BF dictionary
    bf_dict[rec_id] = rec_bf
    
    # Count the number of 1 bits in the Bloom filter
    bf_num_1_bit_list.append(int(rec_bf.count(1)))

  print '  Bloom filter generation took %d sec' % (time.time()-start_time)
  print '    Average number of bits per BF set to 1 and std-dev: %d / %.2f' \
        % (numpy.mean(bf_num_1_bit_list), numpy.std(bf_num_1_bit_list))

  del bf_num_1_bit_list

  return bf_dict

# -----------------------------------------------------------------------------

def get_avrg_num_q_grams(rec_val_list, use_attr_list, q, padded):
  """ Using a list of records extracted from dataset calculate the average
      number of q-grams per record
  """
  
  num_q_gram_per_rec_list = []
  
  qm1 = q-1  # Shorthand
  
  for attr_val_list in rec_val_list:
    
    rec_q_gram_set = set()
    
    for attr_num in use_attr_list:
      attr_val = attr_val_list[attr_num]
      
      attr_val_len = len(attr_val)
      
      if (padded == True):  # Add padding start and end characters
        attr_val = PAD_CHAR*qm1+attr_val+PAD_CHAR*qm1
        attr_val_len += 2*qm1
        
      attr_q_gram_set = set([attr_val[i:i+q] for i in 
                             range(attr_val_len - qm1)])
      
      rec_q_gram_set.update(attr_q_gram_set)
    
    num_q_gram_per_rec_list.append(len(rec_q_gram_set))
  
  avrg_num_q_gram = numpy.mean(num_q_gram_per_rec_list)
  
  return avrg_num_q_gram
      
# -----------------------------------------------------------------------------

def align_freq_bf_attr_val(bf_dict, attr_val_freq_dict, min_freq):
  """Align frequent Bloom filters with frequent attribute values and return a
     list of pairs of BF and attribute values and their frequencies.

     Only BFs and attribute values that occur at least 'min_freq' times will be
     considered, and only BFs and attribute values will be added to the list if
     their frequencies are unique.
  """

  print 'Align frequent BF and frequent attribute values'

  # Get frequencies of all Bloom filters and keep those that occur at least
  # 'min_freq' times
  #
  bf_freq_dict = {}

  for this_bf in bf_dict.itervalues():
    bf_freq_dict[this_bf.to01()] = bf_freq_dict.get(this_bf.to01(), 0) + 1

  sorted_bf_list = []

  for (this_bf, this_bf_freq) in bf_freq_dict.iteritems():
    if (this_bf_freq >= min_freq):
      sorted_bf_list.append((this_bf, this_bf_freq))

  sorted_bf_list.sort(key=lambda t: t[1], reverse=True)

  print '  Number of unique BF with a frequency of at least %d: %d' % \
        (min_freq, len(sorted_bf_list))

  # Get list of frequent attribute values that occur at least 'min_freq' times
  #
  sorted_attr_val_list = []

  for (this_attr_val, this_attr_val_freq) in attr_val_freq_dict.iteritems():
    if (this_attr_val_freq >= min_freq):
      sorted_attr_val_list.append((this_attr_val, this_attr_val_freq))

  sorted_attr_val_list.sort(key=lambda t: t[1], reverse=True)

  print '  Number of unique attribute values with a frequency of at least ' + \
        '%d: %d' % (min_freq, len(sorted_attr_val_list))
  print

  # Now align frequent BF and attribute values as long as their frequencies are
  # unique
  #
  freq_bf_attr_val_list = []

  rank = 0

  max_rank = min(len(sorted_bf_list), len(sorted_attr_val_list))

  # No or a single BF or attribute value found for given minimum frequncy
  # (min_freq) (added by Thilina, extended by Peter)
  #
  if (max_rank == 1):
    this_bf =            sorted_bf_list[0][0]
    this_bf_freq =       sorted_bf_list[0][1]

    this_attr_val =      sorted_attr_val_list[0][0]
    this_attr_val_freq = sorted_attr_val_list[0][1]

    freq_bf_attr_val_list.append((this_bf, this_bf_freq, this_attr_val, 
                                  this_attr_val_freq))

  elif (max_rank > 1):  # At least two values
    this_bf =            sorted_bf_list[rank][0]
    this_bf_freq =       sorted_bf_list[rank][1]

    this_attr_val =      sorted_attr_val_list[rank][0]
    this_attr_val_freq = sorted_attr_val_list[rank][1]

    # Loop down the list of BFs and attribute values ordered by frequency
    #
    while (rank < max_rank):
      next_bf_freq =       sorted_bf_list[rank+1][1]
      next_attr_val_freq = sorted_attr_val_list[rank+1][1]

      if ((this_bf_freq == next_bf_freq) or \
          (this_attr_val_freq == next_attr_val_freq)):
        print 'Warning: Two BF or two attribute values have the same ' + \
              'frequency, stop'
        break  # Exit loop (two BF or two attribute values with same frequency)

      freq_bf_attr_val_list.append((this_bf, this_bf_freq, this_attr_val, 
                                    this_attr_val_freq))
      rank += 1
      
      this_bf =            sorted_bf_list[rank][0]
      this_bf_freq =       sorted_bf_list[rank][1]

      this_attr_val =      sorted_attr_val_list[rank][0]
      this_attr_val_freq = sorted_attr_val_list[rank][1]

  print '  Number of frequent BF and attribute values with unique ' + \
        'frequencies: %d' % (len(freq_bf_attr_val_list))
  print

  return freq_bf_attr_val_list

# -----------------------------------------------------------------------------

def analyse_bf_q_gram_freq(freq_bf_attr_val_list, bf_len, q, num_hash_funct):
  """Conduct a frequency and set-based approach to identify which position in
     Bloom filters represent which q-grams.

     Returns a dictionary which for each BF position contains a dictionary of
     possible q-grams at that position, and numerical values of their
     likelihoods.
  """

  start_time = time.time()

  print 'Analyse set of %d frequent Bloom filters and attribute values' % \
        (len(freq_bf_attr_val_list))

  # For all given frequent attribute values get their sets of q-grams
  #
  attr_val_q_gram_dict = {}

  qm1 = q-1

  for (bf, bf_freq, attr_val, attr_val_freq) in freq_bf_attr_val_list:

    attr_val_len = len(attr_val)
    attr_q_gram_list = [attr_val[i:i+q] for i in range(attr_val_len - qm1)]
    attr_q_gram_set =  set(attr_q_gram_list)

    attr_val_q_gram_dict[attr_val] = attr_q_gram_set

  # Step 1: For each BF position, get a set of possible q-grams assigned to
  #         this position (and a value if their likelihoods), as well as a set
  #         of not possible q-grams for this position
  #
  bf_pos_possible_q_gram_dict =     {}
  bf_pos_not_possible_q_gram_dict = {}

  for (bf, bf_freq, attr_val, attr_val_freq) in freq_bf_attr_val_list:

    attr_q_gram_set = attr_val_q_gram_dict[attr_val]
    num_attr_q_gram = len(attr_q_gram_set)

    for pos in range(len(bf)):  # Analyse all bit positions

      assert bf[pos] in ['0','1'], (bf[pos], type(bf[pos]))

      # Set all not possible q-grams for bit positions with value 0
      #
      if (bf[pos] == '0'):
        this_not_poss_q_gram_set = bf_pos_not_possible_q_gram_dict.get(pos,
                                                                       set())
        for q_gram in attr_q_gram_set:
          this_not_poss_q_gram_set.add(q_gram)

        bf_pos_not_possible_q_gram_dict[pos] = this_not_poss_q_gram_set

      else:  # Bit position is 1
        this_poss_q_gram_dict = bf_pos_possible_q_gram_dict.get(pos, {})

        for q_gram in attr_q_gram_set:
          this_poss_q_gram_dict[q_gram] = \
                 this_poss_q_gram_dict.get(q_gram, 0) + 1.0/num_attr_q_gram

        bf_pos_possible_q_gram_dict[pos] = this_poss_q_gram_dict

  # Now remove for each bit position the not possible q-grams from the possible
  # ones
  #
  num_poss_q_gram_list =     []
  num_not_poss_q_gram_list = []

  # The final dictionary with one dictionary per position containing possible
  # q-grams at that position and a numerical value of their likelihood
  #
  poss_q_gram_bf_pos_map_dict = {}

  for pos in range(bf_len):
    not_poss_q_gram_set = bf_pos_not_possible_q_gram_dict.get(pos, set())
    poss_q_gram_dict =    bf_pos_possible_q_gram_dict.get(pos, {})

    num_poss_q_gram_org = len(poss_q_gram_dict)
    num_not_poss_q_gram = len(not_poss_q_gram_set)

    if (num_not_poss_q_gram > 0) and (num_poss_q_gram_org > 0):
      for not_poss_q_gram in not_poss_q_gram_set:
        if not_poss_q_gram in poss_q_gram_dict:
          del poss_q_gram_dict[not_poss_q_gram]  # An impossible q-gram

    poss_q_gram_bf_pos_map_dict[pos] = poss_q_gram_dict

    num_poss_q_gram_filter = len(poss_q_gram_dict)

    num_not_poss_q_gram_list.append(num_not_poss_q_gram)
    num_poss_q_gram_list.append(num_poss_q_gram_filter)

  print '  Not possible number of q-grams per bit position from 0 bits:'
  print '    Minimum: %d, average: %.1f, maximum: %d' % \
        (min(num_not_poss_q_gram_list), numpy.mean(num_not_poss_q_gram_list),
         max(num_not_poss_q_gram_list))
  print '  Possible number of q-grams per bit position from 1 and 0 bits:'
  print '    Minimum: %d, average: %.1f, maximum: %d' % \
        (min(num_poss_q_gram_list), numpy.mean(num_poss_q_gram_list),
         max(num_poss_q_gram_list))
  print

  return poss_q_gram_bf_pos_map_dict

# -----------------------------------------------------------------------------

def reconstruct_attr_val(attr_val_dict, bf_dict, attr_val_freq_dict,
                         use_num_most_freq_attr_val,
                         poss_q_gram_pos_map_dict,
                         analysis_rec_val_id_dict,
                         plain_num_rec):
  """Reconstruct attribute value from Bloom filters and guessed q-grams mapped
     to positions. Only aim to guess the 'use_num_most_freq_attr_val' most
     frequent attribute values.
  """

  # Get the most frequent attribute values
  #
  sorted_attr_val_list = sorted(attr_val_freq_dict.items(),
                 key=lambda t: t[1], reverse=True)[:use_num_most_freq_attr_val]
  freq_attr_val_list = []
  for (attr_val, freq) in sorted_attr_val_list:
    freq_attr_val_list.append(attr_val)

  # For each frequent value get the set of found matching values
  #
  identified_freq_val_dict = {}
  
  # Dictionary for calcualting the attribute and entity reidentification
  # accuracy
  #
  attack_res_dict = {}

  num_no_guess =        0
  num_correct_1_guess = 0
  num_correct_m_guess = 0
  num_wrong_guess =     0

  print 'Reconstruct attribute values from Bloom filters:'
  print '  Aim to reconstruct %d most frequent attribute values:' % \
        (use_num_most_freq_attr_val)
  print '   ', sorted_attr_val_list[:5], '...', sorted_attr_val_list[-5:]

  for (rec_id, rec_bf) in sorted(bf_dict.iteritems()):

    true_attr_val = attr_val_dict[rec_id]

    if (true_attr_val not in freq_attr_val_list):
      continue  # Not a value we know the true status of

    if (true_attr_val in identified_freq_val_dict):
      continue  # Only process each unique frequent attribute value once

    print '  Record %s has true frequent attribute value "%s"' % \
          (rec_id, true_attr_val)

    # Start with all possible frequent attribute values
    #
    cand_attr_val_set = set(freq_attr_val_list)

    for pos in range(len(rec_bf)):

      if (rec_bf[pos] == 1):
        guessed_q_gram_dict = poss_q_gram_pos_map_dict.get(pos, {})

        if (guessed_q_gram_dict != {}):

          # If none of the guessed q-grams at this position occur in an
          # attribute value we can remove the value from the list of
          # candidates
          #
          for cand_attr_val in list(cand_attr_val_set):

            does_occur = False

            for q_gram in guessed_q_gram_dict:

              if (q_gram in cand_attr_val):
                does_occur = True
                break

            # If none of the guessed q-grams occurs in the attribute value we
            # remove it
            #
            if (does_occur == False):
              cand_attr_val_set.remove(cand_attr_val)

        if (len(cand_attr_val_set) == 0):
          num_no_guess += 1
          break

    identified_freq_val_dict[true_attr_val] = cand_attr_val_set

    if (len(cand_attr_val_set) > 0):
      print '    Guessed value(s) for record %s:' % (str(rec_id)), \
            cand_attr_val_set

      if (true_attr_val in cand_attr_val_set):
        if (len(cand_attr_val_set) == 1):  # Exact 1-to-1 guess
          num_correct_1_guess += 1
        else:
          num_correct_m_guess += 1
      else:
        num_wrong_guess += 1
    
    for cand_attr_val in cand_attr_val_set:
      plain_id_set = analysis_rec_val_id_dict[cand_attr_val]
      
      for plain_id in plain_id_set:
        rec_id_tuple = (rec_id, plain_id)
        attack_res_list = attack_res_dict.get(rec_id_tuple, [])
        attack_res_list.append((rec_bf, true_attr_val, cand_attr_val, 1.0))
        attack_res_dict[rec_id_tuple] = attack_res_list
        
  attack_res_tuple = eval_attack_res.calc_attr_ent_reident_res(attack_res_dict, \
                                                               plain_num_rec)
      
    

  print
  print 'Summary of guessing %d most frequenct attribute values:' % \
        (use_num_most_freq_attr_val)
  print '  Number of correct 1-1 guesses:', num_correct_1_guess
  print '  Number of correct 1-m guesses:', num_correct_m_guess
  print '  Number of wrong guesses:      ', num_wrong_guess
  print '  Number of no guesses:         ', num_no_guess
  print

  return num_correct_1_guess, num_correct_m_guess, num_wrong_guess, \
         num_no_guess, attack_res_tuple

# =============================================================================
# Main program

q =                      int(sys.argv[1])
hash_type =              sys.argv[2].lower()
num_hash_funct =         sys.argv[3]
bf_len =                 int(sys.argv[4])
bf_harden =              sys.argv[5].lower()
bf_encode =              sys.argv[6].lower()
padded =                 eval(sys.argv[7])
min_freq =               int(sys.argv[8])
num_freq_attr_val_list = eval(sys.argv[9])
#
build_data_set_name =    sys.argv[10]
build_rec_id_col =       int(sys.argv[11])
build_col_sep_char =     sys.argv[12]
build_header_line_flag = eval(sys.argv[13])
build_attr_list =        eval(sys.argv[14])
#
analysis_data_set_name =    sys.argv[15]
analysis_rec_id_col =       int(sys.argv[16])
analysis_col_sep_char =     sys.argv[17]
analysis_header_line_flag = eval(sys.argv[18])
analysis_attr_list =        eval(sys.argv[19])
enc_param_list =            eval(sys.argv[20])
harden_param_list =         eval(sys.argv[21])

assert q >= 1, q
assert hash_type in ['dh','rh','edh','th'], hash_type
if num_hash_funct.isdigit():
  num_hash_funct = int(num_hash_funct)
  assert num_hash_funct >= 1, num_hash_funct
else:
  assert num_hash_funct == 'opt', num_hash_funct
assert bf_len > 1, bf_len
assert bf_harden in ['none', 'balance', 'fold', 'rule90', 'mchain', 'salt', 
                     'wxor', 'resample'], \
bf_harden
assert min_freq >= 1, min_freq
for num_freq_attr_val in num_freq_attr_val_list:
  assert num_freq_attr_val >= 1, num_freq_attr_val_list
#
assert build_rec_id_col >= 0, build_rec_id_col
assert build_header_line_flag in [True,False], build_header_line_flag
assert isinstance(build_attr_list, list), build_attr_list
#
assert analysis_rec_id_col >= 0, analysis_rec_id_col
assert analysis_header_line_flag in [True,False], analysis_header_line_flag
assert isinstance(analysis_attr_list, list), analysis_attr_list
#
assert bf_encode in ['abf','clk', 'rbf', 'clkrbf'], bf_encode
#
assert padded in [True, False], padded
#
if (bf_harden == 'fold'):
  if (bf_len%2 != 0):
    raise Exception, 'BF hardening approach "fold" needs an even BF length'

if (bf_harden == 'wxor'):
  window_size = 2 # 3, 4
  harden_param_list = [window_size]

if (len(build_col_sep_char) > 1):
  if (build_col_sep_char == 'tab'):
    build_col_sep_char = '\t'
  elif (build_col_sep_char[0] == '"') and (build_col_sep_char[-1] == '"') and \
     (len(build_col_sep_char) == 3):
    build_col_sep_char = build_col_sep_char[1]
  else:
    print 'Illegal build column separator format:', build_col_sep_char

if (len(analysis_col_sep_char) > 1):
  if (analysis_col_sep_char == 'tab'):
    analysis_col_sep_char = '\t'
  elif (analysis_col_sep_char[0] == '"') and \
     (analysis_col_sep_char[-1] == '"') and \
     (len(analysis_col_sep_char) == 3):
    analysis_col_sep_char = analysis_col_sep_char[1]
  else:
    print 'Illegal analysis column separator format:', analysis_col_sep_char

# Get base names of data sets (remove directory names) for summary output
#
build_base_data_set_name = build_data_set_name.split('/')[-1]
build_base_data_set_name = build_base_data_set_name.replace('.csv', '')
build_base_data_set_name = build_base_data_set_name.replace('.gz', '')
assert ',' not in build_base_data_set_name

analysis_base_data_set_name = analysis_data_set_name.split('/')[-1]
analysis_base_data_set_name = analysis_base_data_set_name.replace('.csv', '')
analysis_base_data_set_name = analysis_base_data_set_name.replace('.gz', '')
assert ',' not in analysis_base_data_set_name

res_file_name = 'bf-attack-results-%s-%s-%s-ent-attr.csv' % \
                (build_base_data_set_name, analysis_base_data_set_name, \
                 today_str)
print
print 'Write results into file:', res_file_name
print
print '-'*80
print

# -----------------------------------------------------------------------------
# Step 1: Load the data sets and extract q-grams for selected attributes
#
start_time = time.time()

# Read the input data file and load all the record values to a list
#
build_rec_val_res_tuple = load_data_set_extract_attr_val(build_data_set_name,
                                                         build_rec_id_col,
                                                         build_attr_list,
                                                         build_col_sep_char,
                                                         build_header_line_flag)

build_rec_val_list      = build_rec_val_res_tuple[0]
build_rec_val_dict      = build_rec_val_res_tuple[1]
build_rec_val_id_dict   = build_rec_val_res_tuple[2]
build_rec_val_freq_dict = build_rec_val_res_tuple[3]
build_attr_name_list    = build_rec_val_res_tuple[4]
                                           
build_load_time = time.time() - start_time
                                           
# Get optimal number of hash functions
#
if (num_hash_funct == 'opt'):
  
  # Get average number of q-grams per record
  #
  build_avrg_num_q_gram = get_avrg_num_q_grams(build_rec_val_list, 
                                               build_attr_list, q, padded)

  # Set number of hash functions to have in average 50% of bits set to 1
  # (reference to published paper? Only in Dinusha's submitted papers) 
  # num_hash_funct = int(math.ceil(0.5 * BF_LEN / \
  #                                math.floor(avrg_num_q_gram)))
  #
  num_hash_funct = int(round(numpy.log(2.0) * float(bf_len) /
                                build_avrg_num_q_gram))

# -----------------------------------------------------------------------------
# Step 2: Extract q-grams and encode them to bloom filters. At the same time
#         apply hardening method if specified
#
start_time = time.time()

build_bf_dict = gen_bloom_filter_dict(build_rec_val_list, build_rec_id_col, 
                                      bf_encode, hash_type, bf_len, 
                                      num_hash_funct, build_attr_list, q, 
                                      padded, bf_harden, enc_param_list, 
                                      harden_param_list)

build_bf_gen_time = time.time() - start_time

# Load plain-text data set and extract q-grams
#
start_time = time.time()

analysis_rec_val_res_tuple = load_data_set_extract_attr_val(analysis_data_set_name,
                                                         analysis_rec_id_col,
                                                         analysis_attr_list,
                                                         analysis_col_sep_char,
                                                         analysis_header_line_flag)

analysis_rec_val_list         = analysis_rec_val_res_tuple[0]
analysis_rec_val_dict         = analysis_rec_val_res_tuple[1]
analysis_rec_val_id_dict      = analysis_rec_val_res_tuple[2]
analysis_rec_val_freq_dict    = analysis_rec_val_res_tuple[3]
analysis_guess_attr_name_list = analysis_rec_val_res_tuple[4]

analysis_load_time = time.time() - start_time

if (build_attr_name_list != analysis_guess_attr_name_list):
  print '** Warning: Different attributes used to encode BF and guessing:'
  print '**   BF encode:', build_attr_name_list
  print '**   Guessing: ', analysis_guess_attr_name_list
# -----------------------------------------------------------------------------
# Step 3: Align frequent Bloom filters with frequent attribute values

# Align frequent BF to frequent attribute values from analysis (different)
# data set
#
analysis_freq_bf_attr_val_list = align_freq_bf_attr_val(build_bf_dict, 
                                              analysis_rec_val_freq_dict,
                                              min_freq)
analysis_num_unique_freq_bf_attr_val = len(analysis_freq_bf_attr_val_list)

# Check if most frequent BF's frequency is higher than 1
# if not end the programme
#
if(len(analysis_freq_bf_attr_val_list) > 0):
  
  # -----------------------------------------------------------------------------
  # Now loop over different numbers of most frequent values
  #
  for num_freq_attr_val in num_freq_attr_val_list:
  
    print 'Analyse BF and attribute values using %d most frequent values only' \
          % (num_freq_attr_val)
  
    # Limit to the most frequent BFs and attribute values
    #
    if (len(analysis_freq_bf_attr_val_list) > num_freq_attr_val):
      analysis_freq_bf_attr_val_list = \
                            analysis_freq_bf_attr_val_list[:num_freq_attr_val]
  
    # ---------------------------------------------------------------------------
    # Step 4: Analyse Bloom filters using attribute value frequencies
    #
    start_time = time.time()
  
    # Now analyse on the analysis data set
    #
    analysis_poss_q_gram_bf_pos_map_dict = \
                         analyse_bf_q_gram_freq(analysis_freq_bf_attr_val_list,
                                                bf_len, q, num_hash_funct)
  
    analysis_num_correct_1_guess, analysis_num_correct_m_guess, \
              analysis_num_wrong_guess, analysis_num_no_guess, \
              attack_res_tuple = \
                     reconstruct_attr_val(build_rec_val_dict,
                                          build_bf_dict,
                                          analysis_rec_val_freq_dict,
                                          num_freq_attr_val,
                                          analysis_poss_q_gram_bf_pos_map_dict,
                                          analysis_rec_val_id_dict,
                                          len(analysis_rec_val_dict))
  
    analysis_analyse_time = time.time() - start_time
    
    
    attr_reident_res_dict        = attack_res_tuple[0]
    attr_reident_single_res_dict = attack_res_tuple[1]
    ent_reident_res_dict         = attack_res_tuple[2]
    ent_reident_single_res_dict  = attack_res_tuple[3]
    prob_susc_res_dict           = attack_res_tuple[4] 
    reident_time                 = attack_res_tuple[5]
    
    attr_reident_1_1    = attr_reident_res_dict['1-1'] if '1-1' in attr_reident_res_dict else 0
    attr_reident_1_1_p  = attr_reident_res_dict['1-1-p'] if '1-1-p' in attr_reident_res_dict else 0
    attr_reident_1_1_w  = attr_reident_res_dict['1-1-w'] if '1-1-w' in attr_reident_res_dict else 0
    attr_reident_1_m    = attr_reident_res_dict['1-m'] if '1-m' in attr_reident_res_dict else 0
    attr_reident_1_m_p  = attr_reident_res_dict['1-m-p'] if '1-m-p' in attr_reident_res_dict else 0
    attr_reident_1_m_w  = attr_reident_res_dict['1-m-w'] if '1-m-w' in attr_reident_res_dict else 0
    attr_reident_m_1    = attr_reident_res_dict['m-1'] if 'm-1' in attr_reident_res_dict else 0
    attr_reident_m_1_p  = attr_reident_res_dict['m-1-p'] if 'm-1-p' in attr_reident_res_dict else 0
    attr_reident_m_1_w  = attr_reident_res_dict['m-1-w'] if 'm-1-w' in attr_reident_res_dict else 0
    attr_reident_m_m    = attr_reident_res_dict['m-m'] if 'm-m' in attr_reident_res_dict else 0
    attr_reident_m_m_p  = attr_reident_res_dict['m-m-p'] if 'm-m-p' in attr_reident_res_dict else 0
    attr_reident_m_m_w  = attr_reident_res_dict['m-m-w'] if 'm-m-w' in attr_reident_res_dict else 0
    #
    attr_reident_sin_1_1  = attr_reident_single_res_dict['1-1'] if '1-1' in attr_reident_single_res_dict else 0
    attr_reident_sin_1_m  = attr_reident_single_res_dict['1-m'] if '1-m' in attr_reident_single_res_dict else 0
    attr_reident_sin_m_1  = attr_reident_single_res_dict['m-1'] if 'm-1' in attr_reident_single_res_dict else 0
    attr_reident_sin_m_m  = attr_reident_single_res_dict['m-m'] if 'm-m' in attr_reident_single_res_dict else 0
    attr_reident_sin_wrng = attr_reident_single_res_dict['wrng'] if 'wrng' in attr_reident_single_res_dict else 0
    #
    ent_reident_1_1   = ent_reident_res_dict['1-1'] if '1-1' in ent_reident_res_dict else 0
    ent_reident_1_1_p = ent_reident_res_dict['1-1-p'] if '1-1-p' in ent_reident_res_dict else 0
    ent_reident_1_1_w = ent_reident_res_dict['1-1-w'] if '1-1-w' in ent_reident_res_dict else 0
    ent_reident_1_m   = ent_reident_res_dict['1-m'] if '1-m' in ent_reident_res_dict else 0
    ent_reident_1_m_p = ent_reident_res_dict['1-m-p'] if '1-m-p' in ent_reident_res_dict else 0
    ent_reident_1_m_w  = ent_reident_res_dict['1-m-w'] if '1-m-w' in ent_reident_res_dict else 0 
    ent_reident_m_1   = ent_reident_res_dict['m-1'] if 'm-1' in ent_reident_res_dict else 0
    ent_reident_m_1_p = ent_reident_res_dict['m-1-p'] if 'm-1-p' in ent_reident_res_dict else 0
    ent_reident_m_1_w = ent_reident_res_dict['m-1-w'] if 'm-1-w' in ent_reident_res_dict else 0
    ent_reident_m_m   = ent_reident_res_dict['m-m'] if 'm-m' in ent_reident_res_dict else 0
    ent_reident_m_m_p = ent_reident_res_dict['m-m-p'] if 'm-m-p' in ent_reident_res_dict else 0
    ent_reident_m_m_w = ent_reident_res_dict['m-m-w'] if 'm-m-w' in ent_reident_res_dict else 0
    #
    ent_reident_sin_1_1  = ent_reident_single_res_dict['1-1'] if '1-1' in ent_reident_single_res_dict else 0
    ent_reident_sin_1_m  = ent_reident_single_res_dict['1-m'] if '1-m' in ent_reident_single_res_dict else 0
    ent_reident_sin_m_1  = ent_reident_single_res_dict['m-1'] if 'm-1' in ent_reident_single_res_dict else 0
    ent_reident_sin_m_m  = ent_reident_single_res_dict['m-m'] if 'm-m' in ent_reident_single_res_dict else 0
    ent_reident_sin_wrng = ent_reident_single_res_dict['wrng'] if 'wrng' in ent_reident_single_res_dict else 0
    
    
    
    # ---------------------------------------------------------------------------
    # Print summary results
    #
    print '#### ---------------------------------------------'
    print '#### Run at:', time.strftime("%Y%m%d %H:%M:%S", time.localtime())
    print '####  ', auxiliary.get_memory_usage()
    print '####   Time used build (load and q-gram gen / BF gen):   ' \
          + '%d / %d sec' % (build_load_time, build_bf_gen_time)
    #
    print '####   Time used analysis (load and q-gram gen / BF gen / ' \
        + 'analysis): %d / -- / %d sec' % (analysis_load_time, \
                                           analysis_analyse_time)
    print '#### Build data set: %s' % (build_base_data_set_name)
    print '####   Number of records: %d' % (len(build_rec_val_dict))
    print '####   Attribute(s) used: %s' % (str(build_attr_name_list))
    #
    print '#### Analysis data set: %s' % (analysis_base_data_set_name)
    print '####   Number of records: %d' % (len(analysis_rec_val_dict))
    print '####   Attribute(s) used: %s' % (str(analysis_guess_attr_name_list))
    print '#### Minimum attribute frequency for analysis: %d' % \
          (min_freq)
    #
    print '#### BF len: %d' % (bf_len)
    print '####   Num hash funct: %d' % (num_hash_funct)
  
    print '####   q: %d' % (q)
    print '####   BF hardening: %s' % (bf_harden)
    print '####   Hashing type: %s' % \
          ({'dh':'Double hashing', 'rh':'Random hashing', 
            'edh':'Enhanced Double hashing', 'th':'Triple hashing'}[hash_type])
    print '#### Number of unique frequent BF and attribute values ' + \
          '(analysis): %d' % (analysis_num_unique_freq_bf_attr_val)
  
    print '#### Number of most frequent attribute values to reconstruct: %d' % \
          (num_freq_attr_val)
    print '#### Re-identification on analysis data set:'
    print '####   Number of correct 1-1 guesses:', analysis_num_correct_1_guess
    print '####   Number of correct 1-m guesses:', analysis_num_correct_m_guess
    print '####   Number of wrong guesses:      ', analysis_num_wrong_guess
    print '####   Number of no guesses:         ', analysis_num_no_guess
    print '####'
  
    # ---------------------------------------------------------------------------
    # Write results into a CSV file for analysis
  
    today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
    
    # Generate header line with column names
    #
    header_list = ['today_time_str','q', 'hash_type', 'num_hash_funct', \
                   'bf_len', 'bf_encode', 'padded', \
                   'bf_harden', 'min_freq', 'num_freq_attr_val', \
                   'build_data_set_name', 'build_attr_list', \
                   'analysis_data_set_name', 'analysis_attr_list', \
                   'build_load_time', 'build_bf_gen_time',
                   #
                   'analysis_load_time',
                   'analysis_analyse_time', 'memo_use', \
                   'analysis_num_correct_1', \
                   'analysis_num_correct_m', 'analysis_num_wrong', \
                   'analysis_num_no',]
    
    attak_res_header = ['max_ps_val_all_assign', 'min_ps_val_all_assign', 
                      'mean_ps_val_all_assign', 'median_ps_val_all_assign', 
                      'marketer_ps_val_all_assign',
                      #
                      'attr_reident_1_1', 'attr_reident_1_1_p', 'attr_reident_1_1_w',
                      'attr_reident_1_m', 'attr_reident_1_m_p', 'attr_reident_1_m_w',
                      'attr_reident_m_1', 'attr_reident_m_1_p', 'attr_reident_m_1_w',
                      'attr_reident_m_m', 'attr_reident_m_m_p', 'attr_reident_m_m_w',
                      #
                      'attr_reident_sin_1_1', 'attr_reident_sin_1_m', 
                      'attr_reident_sin_m_1', 'attr_reident_sin_m_m',
                      'attr_reident_sin_wrng',
                      #
                      'ent_reident_1_1', 'ent_reident_1_1_p', 'ent_reident_1_1_w',
                      'ent_reident_1_m', 'ent_reident_1_m_p', 'ent_reident_1_m_w',
                      'ent_reident_m_1', 'ent_reident_m_1_p', 'ent_reident_m_1_w',
                      'ent_reident_m_m', 'ent_reident_m_m_p', 'ent_reident_m_m_w',
                      #
                      'ent_reident_sin_1_1', 'ent_reident_sin_1_m', 
                      'ent_reident_sin_m_1', 'ent_reident_sin_m_m',
                      'ent_reident_sin_wrng',
                      #
                      'res_eval_time']
    
    header_list += attak_res_header
  
    # Check if the result file exists, if it does append, otherwise create
    #
    if (not os.path.isfile(res_file_name)):
      csv_writer = csv.writer(open(res_file_name, 'w'))
  
      csv_writer.writerow(header_list)
  
    else:  # Append results to an existing file
      csv_writer = csv.writer(open(res_file_name, 'a'))
  
  #=============================================================================
  #   build_attr_list_str = str(build_attr_list)[1:-1].replace(',','-')
  #   build_attr_list_str = build_attr_list_str.replace(' ', '')
  # 
  #   analysis_attr_list_str = str(analysis_attr_list)[1:-1].replace(',','-')
  #   analysis_attr_list_str = analysis_attr_list_str.replace(' ', '')
  #=============================================================================
  
    res_list = [today_time_str, q, hash_type, num_hash_funct, bf_len, 
                bf_encode, padded, bf_harden,
                min_freq, num_freq_attr_val, build_base_data_set_name,
                str(build_attr_name_list), analysis_base_data_set_name,
                str(analysis_guess_attr_name_list),
                build_load_time, build_bf_gen_time,
                #
                analysis_load_time, analysis_analyse_time,
                auxiliary.get_memory_usage_val(),
                analysis_num_correct_1_guess, analysis_num_correct_m_guess,
                analysis_num_wrong_guess, analysis_num_no_guess,]
    
    attack_res_list = [prob_susc_res_dict['max-ps'], prob_susc_res_dict['min-ps'],
                       prob_susc_res_dict['avrg-ps'], prob_susc_res_dict['med-ps'],
                       prob_susc_res_dict['makt-ps'],
                       #
                       attr_reident_1_1, attr_reident_1_1_p, attr_reident_1_1_w, 
                       attr_reident_1_m, attr_reident_1_m_p, attr_reident_1_m_w, 
                       attr_reident_m_1, attr_reident_m_1_p, attr_reident_m_1_w, 
                       attr_reident_m_m, attr_reident_m_m_p, attr_reident_m_m_w,
                       #
                       attr_reident_sin_1_1, attr_reident_sin_1_m, attr_reident_sin_m_1, 
                       attr_reident_sin_m_m, attr_reident_sin_wrng,
                       #
                       ent_reident_1_1, ent_reident_1_1_p, ent_reident_1_1_w, 
                       ent_reident_1_m, ent_reident_1_m_p, ent_reident_1_m_w,
                       ent_reident_m_1, ent_reident_m_1_p, ent_reident_m_1_w,
                       ent_reident_m_m, ent_reident_m_m_p, ent_reident_m_m_w,
                       #
                       ent_reident_sin_1_1, ent_reident_sin_1_m, ent_reident_sin_m_1,
                       ent_reident_sin_m_m, ent_reident_sin_wrng,
                       #
                       reident_time,
                       ]
    
    res_list += attack_res_list
      
  
    assert len(res_list) == len(header_list)
  
    csv_writer.writerow(res_list)
  
else:
  analysis_analyse_time = 0
  analysis_num_correct_1_guess = 0
  analysis_num_correct_m_guess = 0
  analysis_num_wrong_guess = 0
  analysis_num_no_guess = 0

  # ---------------------------------------------------------------------------
  # Print summary results
  #
  print '#### ---------------------------------------------'
  print '#### Run at:', time.strftime("%Y%m%d %H:%M:%S", time.localtime())
  print '####  ', auxiliary.get_memory_usage()
  print '####   Time used build (load and q-gram gen / BF gen):   ' \
        + '%d / %d sec' % (build_load_time, build_bf_gen_time)
  #
  print '####   Time used analysis (load and q-gram gen / BF gen / ' \
      + 'analysis): %d / -- / %d sec' % (analysis_load_time, \
                                         analysis_analyse_time)
  print '#### Build data set: %s' % (build_base_data_set_name)
  print '####   Number of records: %d' % (len(build_rec_val_dict))
  print '####   Attribute(s) used: %s' % (str(build_attr_name_list))
  #
  print '#### Analysis data set: %s' % (analysis_base_data_set_name)
  print '####   Number of records: %d' % (len(analysis_rec_val_dict))
  print '####   Attribute(s) used: %s' % (str(analysis_guess_attr_name_list))
  print '#### Minimum attribute frequency for analysis: %d' % \
        (min_freq)
  #
  print '#### BF len: %d' % (bf_len)
  print '####   Num hash funct: %d' % (num_hash_funct)

  print '####   q: %d' % (q)
  print '####   BF hardening: %s' % (bf_harden)
  print '####   Hashing type: %s' % \
        ({'dh':'Double hashing', 'rh':'Random hashing', 
          'edh':'Enhanced double hashing', 'th':'Triple hashing'}[hash_type])
  print '#### Number of unique frequent BF and attribute values ' + \
        '(analysis): %d' % (analysis_num_unique_freq_bf_attr_val)

  print '#### Number of most frequent attribute values to reconstruct: %d' % \
        (num_freq_attr_val)
  print '#### Re-identification on analysis data set:'
  print '####   Number of correct 1-1 guesses:', analysis_num_correct_1_guess
  print '####   Number of correct 1-m guesses:', analysis_num_correct_m_guess
  print '####   Number of wrong guesses:      ', analysis_num_wrong_guess
  print '####   Number of no guesses:         ', analysis_num_no_guess
  print '####'

  # ---------------------------------------------------------------------------
  # Write results into a CSV file for analysis

  today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
  
  res_file_name_err = 'bf-attack-results-%s-%s-error.csv' % \
                (build_base_data_set_name, analysis_base_data_set_name)
  
  # Generate header line with column names
  #
  header_list = ['today_time_str','q', 'hash_type', 'num_hash_funct', \
                 'bf_len', 'bf_encode',\
                 'bf_harden', 'min_freq', 'num_freq_attr_val', \
                 'build_data_set_name', 'build_attr_list', \
                 'analysis_data_set_name', 'analysis_attr_list', \
                 'build_load_time', 'build_bf_gen_time',
                 #
                 'analysis_load_time',
                 'analysis_analyse_time', 'memo_use', \
                 'analysis_num_correct_1', \
                 'analysis_num_correct_m', 'analysis_num_wrong', \
                 'analysis_num_no']
#                 'analysis_estim_k1', 'analysis_estim_k2']

  # Check if the result file exists, if it does append, otherwise create
  #
  if (not os.path.isfile(res_file_name_err)):
    csv_writer = csv.writer(open(res_file_name_err, 'w'))

    csv_writer.writerow(header_list)

  else:  # Append results to an existing file
    csv_writer = csv.writer(open(res_file_name_err, 'a'))

#===============================================================================
#   build_attr_list_str = str(build_attr_list)[1:-1].replace(',','-')
#   build_attr_list_str = build_attr_list_str.replace(' ', '')
# 
#   analysis_attr_list_str = str(analysis_attr_list)[1:-1].replace(',','-')
#   analysis_attr_list_str = analysis_attr_list_str.replace(' ', '')
#===============================================================================

  res_list = [today_time_str, q, hash_type, num_hash_funct, bf_len, 
              bf_encode, bf_harden,
              min_freq, num_freq_attr_val, build_base_data_set_name,
              str(build_attr_name_list), analysis_base_data_set_name,
              str(analysis_guess_attr_name_list),
              build_load_time, build_bf_gen_time,
              #
              analysis_load_time, analysis_analyse_time,
              auxiliary.get_memory_usage_val(),
              analysis_num_correct_1_guess, analysis_num_correct_m_guess,
              analysis_num_wrong_guess, analysis_num_no_guess]

  assert len(res_list) == len(header_list)

  csv_writer.writerow(res_list)

# End.
