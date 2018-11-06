#!/usr/bin/env python3 
import sys
import itertools
import random
import argparse
import datetime
import statistics
from operator import itemgetter
from itertools import chain

chr_range = 'AaBbCcDdEeFf'

"""# GLOSSARY and INFO:
Aneuploid pairing bias parameter: applied to decrease the transmission of the monosome from parents with 3:1 complements.
Default set to 4, see paper for details.

Pairing fidelity value:  Stringency of homologue pairing that is encoded as a single digit across all chromosomes, 
e.g., 8=80%, 9=90% and 0=100%.

Chromosome group: Chromosomes that are homologous or homeologous, e.g. have the same letter in upper or lower case
(e.g., 'C4C4c4c4'). Note that the chromosome group was constrained to always having 4 chromosomes in 2:2, 1:3, or 0:4 
homeologue ratios.

output_text_file_column_names = ["Generation","End_generation","Max_pop_size","SEED_VIABILITY","SURVIVAL_TO_FLOWERING",\
"MAX_SEED_SET", "CORRECT_PAIRING_PROBABILITY","Total_stable_individuals","Total_germinated_euploids",\
"Total_germinated_3_1_aneupoids","Total_germinated_4_0_aneupoids","Total_flowering_euploids",\
"Total_flowering_3_1_aneupoids","Total_flowering_4_0_aneupoids","A_tet_count","B_tet_count","C_tet_count",\
"D_tet_count","E_tet_count","F_tet_count","G_tet_count","H_tet_count","I_tet_count","J_tet_count","K_tet_count",\
"L_tet_count","balanced_all_B_and_U","unbalanced_all_B_and_U","nulli_all_B_and_U","balanced_all_B_and_U_and_N",\
"unbalanced_all_B_and_U_and_N","nulli_all_B_and_U_and_N","balanced_flowering_B_and_U","unbalanced_flowering_B_and_U",\
"nulli_flowering_B_and_U","balanced_flowering_B_and_U_and_N","unbalanced_flowering_B_and_U_and_N",\
"nulli_flowering_B_and_U_and_N"]

"""


def karyotype_table_lookup(pairing_fidelity):
    """select from a dictionary of predefined karyotypes to initialize a population with a single founder
    :arg pairing_fidelity comes from the command line as a string
    :type pairing_fidelity: str """
    karyotypes = {'10': [['A1A1a1a1', 'B1B1b1b1', 'C1C1c1c1', 'D1D1d1d1', 'E1E1e1e1', 'F1F1f1f1']],
                  '20': [['A2A2a2a2', 'B2B2b2b2', 'C2C2c2c2', 'D2D2d2d2', 'E2E2e2e2', 'F2F2f2f2']],
                  '30': [['A3A3a3a3', 'B3B3b3b3', 'C3C3c3c3', 'D3D3d3d3', 'E3E3e3e3', 'F3F3f3f3']],
                  '40': [['A4A4a4a4', 'B4B4b4b4', 'C4C4c4c4', 'D4D4d4d4', 'E4E4e4e4', 'F4F4f4f4']],
                  '50': [['A5A5a5a5', 'B5B5b5b5', 'C5C5c5c5', 'D5D5d5d5', 'E5E5e5e5', 'F5F5f5f5']],
                  '60': [['A6A6a6a6', 'B6B6b6b6', 'C6C6c6c6', 'D6D6d6d6', 'E6E6e6e6', 'F6F6f6f6']],
                  '70': [['A7A7a7a7', 'B7B7b7b7', 'C7C7c7c7', 'D7D7d7d7', 'E7E7e7e7', 'F7F7f7f7']],
                  '80': [['A8A8a8a8', 'B8B8b8b8', 'C8C8c8c8', 'D8D8d8d8', 'E8E8e8e8', 'F8F8f8f8']],
                  '90': [['A9A9a9a9', 'B9B9b9b9', 'C9C9c9c9', 'D9D9d9d9', 'E9E9e9e9', 'F9F9f9f9']],
                  '100': [['A0A0a0a0', 'B0B0b0b0', 'C0C0c0c0', 'D0D0d0d0', 'E0E0e0e0', 'F0F0f0f0']]
                  }
    if pairing_fidelity not in karyotypes:
        print("Specified karyotype not found: ", args.starting_karyotype)
        quit()
    else:
        return karyotypes[pairing_fidelity]


class GenerationState:
    def __init__(self, viable_seeds_codes, reproducing_individuals_codes, stable_scores, tetrasomic_dict):
        """Summary stats that are collected at each generation
            :arg viable_seeds_codes holds karyotype codes from individuals at viable seed stage,
                B=balanced, U=3:1, N=4:0
            :type viable_seeds_codes: list[summarised karyotypes]
            :arg reproducing_individuals_codes holds karyotype codes from reproducing individuals stage
            :type reproducing_individuals_codes: list[summarised karyotypes]
            :arg stable_scores holds number of fully stable individuals, i.e. '0' on all chromosomes in karyotype
            :type stable_scores: int
            :arg tetrasomic_dict holds dictionary with counts of tetrasomic chromosomes
            :type tetrasomic_dict: dict
            """
        self.codes_for_viable_seeds = viable_seeds_codes
        self.codes_for_reproducing_individuals = reproducing_individuals_codes
        self.count_of_stable_mature_individuals = stable_scores
        self.tetrasomic_dict = tetrasomic_dict


class KaryotypeSimulation:
    def __init__(self, report_on_germinated_karyotypes, report_on_adult_karyotypes, aneuploid_pairing_bias):
        self.aneuploid_pairing_bias = aneuploid_pairing_bias
        self.generation_history = []  # the main set of state information.  One GenerationState per generation
        self.pop_size = 0  # this prevents double doubling on first generation
        self.n_generations = args.generations
        self.all_seeds = []
        self.report_on_germinated_karyotypes = report_on_germinated_karyotypes
        self.report_on_adult_karyotypes = report_on_adult_karyotypes
        self.initialise_population()

    def initialise_population(self):
        """Add individuals with defined karyotypes to population"""
        self.n_generations = self.n_generations + 1 # add 1 to account for pre-meiosis generation 'zero'
        if args.starting_karyotype in ['10', '20', '30', '40', '50', '60', '70', '80', '90', '100']:
            # for population starting from a single individual, load karyotype
            self.all_seeds = [karyotype_table_lookup(args.starting_karyotype)]
        else:
            # for mix of low and high stringency karyotypes, needs following convention, e.g., PD_50_80_5_5
            if args.starting_karyotype.count('_') != 4:
                print("--starting_karyotype not defined properly: ", args.starting_karyotype)
                exit()
            else:
                numbers_of_defined_individuals_list = args.starting_karyotype.split('_')
                lower_stringency_number_of_indivs = int(numbers_of_defined_individuals_list[3])
                higher_stringency_number_of_indivs = int(numbers_of_defined_individuals_list[4])
                # get real pop size
                self.pop_size = lower_stringency_number_of_indivs + higher_stringency_number_of_indivs
                # throw error if size exceeds upper limit of pop size
                if self.pop_size > args.max_pop_size:
                    print("Number of specified individuals exceeds --max_pop_size", file=sys.stderr)
                    exit()
                # for a mixed population define lower and higher stringency karyotypes
                lis0 = karyotype_table_lookup(numbers_of_defined_individuals_list[1])
                lis1 = karyotype_table_lookup(numbers_of_defined_individuals_list[2])
                self.all_seeds = ([lis0] * lower_stringency_number_of_indivs) + \
                                 ([lis1] * higher_stringency_number_of_indivs)
        if not self.all_seeds:
            print("Founder individuals not loaded. Check: --starting_karyotype")
            exit()
        print("Founder karyotype(s):\n", self.all_seeds)

    def _report_on_generation(self, germinated_seeds, reproducing_individuals):
        if self.report_on_germinated_karyotypes:
            print('\nIndividuals which germinated')
            for i in germinated_seeds:
                print(i)
            print('\nGerminated individuals (karyotype codes)')
            print(code_chromosome_stoichiometry(germinated_seeds))
        if self.report_on_adult_karyotypes:
            print('\nSurviving Adults')
            for i in reproducing_individuals:
                print(i)
            print('\nSurviving Adults (karyotype codes)')
            print(code_chromosome_stoichiometry(reproducing_individuals))


    def run_simulation(self):
        for generation_i in range(self.n_generations):
            viable_seeds_listing = apply_selection_to_seeds(self.all_seeds)
            self.all_seeds = []

            germinated_seeds = random_sib_survival(viable_seeds_listing)
            germinated_seeds_snapshot = code_chromosome_stoichiometry(germinated_seeds)

            established_plants = ranked_survival_to_flowering(germinated_seeds)
            random.shuffle(established_plants)
            self.pop_size = determine_current_population_carrying_capacity(self.pop_size)
            reproducing_individuals = established_plants[0:self.pop_size] # random survival to flowering

            reproducing_individuals_snapshot = code_chromosome_stoichiometry(reproducing_individuals)
            stable_reproducing_individuals_count = count_stable_indivs(reproducing_individuals)
            tetrasomic_counts = count_tetrasomic_indivs(reproducing_individuals)

            gamete_listing = [meiosis(individual, self.aneuploid_pairing_bias) for individual in reproducing_individuals]

            for individual in gamete_listing:
                self.all_seeds.append(dip_list(individual))
            current_generation = GenerationState(germinated_seeds_snapshot, reproducing_individuals_snapshot,
                                                 stable_reproducing_individuals_count, tetrasomic_counts)
            self.generation_history.append(current_generation)
            print(generation_i, end=' ', flush=True)  # Status indicator for user
            self._report_on_generation(germinated_seeds, reproducing_individuals)


def count_stable_indivs(list_of_karyotypes):
    """count meiotically stable karyotypes (with zeros encoded on all chromosomes)
    :arg list_of_karyotypes
    :type list_of_karyotypes: list of lists
    """
    stable_count = 0
    for kary_group in list_of_karyotypes:
        if ''.join(kary_group).count('0') == 4 * 6:
            stable_count += 1
    return stable_count


def count_tetrasomic_indivs(lis) -> dict:
    """ Count number of times that a chromosome is tetrasomic (present in four copies)
    :returns counts_of_tetrasomic_chromosomes"""
    counts_of_tetrasomic_chromosomes = {k: 0 for k in chr_range}

    for kary_group in lis:
        for index, chr_type in enumerate(chr_range):
            if kary_group[index // 2].count(chr_type) == 4:
                counts_of_tetrasomic_chromosomes[chr_type] += 1
    return counts_of_tetrasomic_chromosomes


def random_sib_survival(viable_progeny_listing):
    """ Randomly downsample each set of siblings according to --sibling_survival_cutoff parameter
        and flatten 'progeny lists' into 'population list'
    :param viable_progeny_listing holds a list of sibling kayotypes for each parent in population
    :type viable_progeny_listing: list of lists of lists
    :returns flattened list
    """
    individuals_listing = []
    for lst in viable_progeny_listing:
        for li in lst[0:args.sibling_survival_cutoff]:
            individuals_listing.append(li)
    random.shuffle(individuals_listing)
    return individuals_listing


def aneuploidy_code_for_chr_count(chr_count):
    """ Output a letter code based on chromosome copy number (0,1,2,3,4,5)
    n=numerical aneuploid
    N=nulli-tetrasomic
    B=Balanced
    U=mono-trisomic
    X=double nullisomic
    """
    return {'00': 'X', '10': 'n',  '20': 'n', '30': 'n', '40': 'N', '50': 'n', '60': 'n',
            '01': 'n', '11': 'n',  '21': 'n', '31': 'U', '41': 'n', '51': 'n', '61': 'n',
            '02': 'n', '12': 'n',  '22': 'B', '32': 'n', '42': 'n', '52': 'n', '62': 'n',
            '03': 'n', '13': 'U',  '23': 'n', '33': 'n', '43': 'n', '53': 'n', '63': 'n',
            '04': 'N', '14': 'n',  '24': 'n', '34': 'n', '44': 'n', '54': 'n', '64': 'n',
            '05': 'n', '15': 'n',  '25': 'n', '35': 'n', '45': 'n', '55': 'n', '65': 'n',
            '06': 'n', '16': 'n',  '26': 'n', '36': 'n', '46': 'n', '56': 'n', '66': 'n'}[chr_count]


def code_chromosome_stoichiometry(population_karyotypes):
    """For the whole population, turn the karyotype strings into a string showing balanced versus
    unbalanced chromosome groups.
    :arg population_karyotypes: list of karyotypes.  Each karyotype is a list of
    strings, one string for each chromosome group.
    :type population_karyotypes: list[list[str]]
    """
    group_stoichiometry_status = []
    for karyotype in population_karyotypes:
        code_Aa = aneuploidy_code_for_chr_count(str(karyotype[0].count('A'))+str((karyotype[0].count('a'))))
        code_Bb = aneuploidy_code_for_chr_count(str(karyotype[1].count('B'))+str((karyotype[1].count('b'))))
        code_Cc = aneuploidy_code_for_chr_count(str(karyotype[2].count('C'))+str((karyotype[2].count('c'))))
        code_Dd = aneuploidy_code_for_chr_count(str(karyotype[3].count('D'))+str((karyotype[3].count('d'))))
        code_Ee = aneuploidy_code_for_chr_count(str(karyotype[4].count('E'))+str((karyotype[4].count('e'))))
        code_Ff = aneuploidy_code_for_chr_count(str(karyotype[5].count('F'))+str((karyotype[5].count('f'))))
        group_stoichiometry_status.append(''.join((code_Aa, code_Bb, code_Cc, code_Dd, code_Ee, code_Ff)))
        # example: ['BBBBBU', 'BBUBBB', 'BBBBBB', 'BBUBBB']
    return group_stoichiometry_status


def meiosis(parent_karyotype, aneuploid_pairing_bias):
    """ Generate all possible random chromosome pairs in gametes, then weights the outcomes by pairing
    fidelity. Takes the chromosome composition of an individual and produces the set of possible gametes
    through meiosis.
    Note: Homeologous pairing produces chromosome characters at specific positions:
    Tetrasomic inheritance products are on outer positions 0 and 5 in array.
    Disomic inheritance products are at inner positions 1-4 in array
    :arg parent_karyotype holds parent's chromosomes,
        e.g. ['A5A5a5a5', 'B5B5b5b5', 'C5C5c5c5', 'D5D5d5d5', 'E5E5e5e5', 'F5F5f5f5']
    :type parent_karyotype: list[chromosome groups]
    :arg aneuploid_pairing_bias holds number which in the case of 3:1 ratios controlling strength of skew
        (i.e. increased 0:2 transmission from trisomic chromosome )
    :type aneuploid_pairing_bias: int
    """
    possible_gametic_combinations = []
    for chr_group in parent_karyotype:
        disomic_count, tetrasomic_count, total_count = homeolog_ratio_and_weighting_and_total(chr_group)
        letter = chr_group[0]
        balanced = chr_group.count(letter.upper()) == 2 and chr_group.count(letter.lower()) == 2 # check 2:2 ratio
        if total_count == 4:
            if balanced:
                group_homeologue_list = generate_all_haploid_chr_combinations(chr_group)
                numerical_aneuploid_list = tetrasomic_split_listing(chr_group)
                possible_gametic_combinations.append(
                    (group_homeologue_list[1:5]* disomic_count*args.non_numerical_multiplier) + #(1) homologous pairing products
                    (group_homeologue_list[0:1]* tetrasomic_count*args.non_numerical_multiplier) + #(2) homeologous pairing products
                    (group_homeologue_list[5:6]* tetrasomic_count*args.non_numerical_multiplier) + #(3) homeologous pairing products
                    (list(chain.from_iterable(numerical_aneuploid_list[:]))))   #(4) numerical aneuploid list
            else:  # unbalanced 1:3 or 0:4 composition
                group_homeologue_list = generate_all_haploid_chr_combinations(chr_group)
                # In 1:3 situations, need to boost numbers of 0:2 gametes due to non-disjunction of monosomes.
                # Non-disjunction will be highest where pairing stringency is highest
                lis_of_nulli_disome_gametes = []
                for pairing in group_homeologue_list:
                    if pairing[0:1] == pairing[2:3]:
                        lis_of_nulli_disome_gametes.append(pairing)
                resulting_aneuploid_count = disomic_count * aneuploid_pairing_bias  # homeologous pairing bias
                # increase the number of unbalanced gametes.  See paper for rationale on using an integer value of 4.
                lis_of_nulli_disome_gametes *= resulting_aneuploid_count
                possible_gametic_combinations.append(group_homeologue_list + lis_of_nulli_disome_gametes)
        if total_count == 3:
            possible_gametic_combinations.append(list(chain.from_iterable(trisomic_split_listing(chr_group)[:]))) # TODO: check if bias is needed
        if total_count == 5:
            possible_gametic_combinations.append(list(chain.from_iterable(pentasomic_split_listing(chr_group)[:]))) # TODO: check if bias is needed
    return possible_gametic_combinations


def generate_all_haploid_chr_combinations(chr_group):
    """ Generate list of all six possible homologue/homeologue pairs.
    Inner chromosome combinations (1,2,3 and 4 in list) result from homologous pairing.
    Outer chromosome combinations (0 and 6 in list) result from homeologous pairing.
    :arg chr_group e.g. 'A8A8a8a8'
    :type chr_group: str
    """
    group_homeologue_list = []
    chr_group = reorder_balanced_2plus2(chr_group)
    chrm_combs = [chr_group[0:2], chr_group[2:4], chr_group[4:6], chr_group[6:8]]
    for pair in itertools.combinations(chrm_combs, 2):
        group_homeologue_list.append(pair[0] + pair[1])
    return group_homeologue_list


def trisomic_split_listing(chr_group):
    monosome_lis = []
    gamete_lis = []
    chr_group_ls = [chr_group[i:i+2] for i in range(0, len(chr_group), 2)]
    for i in range(len(chr_group_ls)):
        popped_chrm = chr_group_ls.pop(-1)
        monosome_lis.append(popped_chrm)
        monosome_lis.append(''.join(chr_group_ls))
        chr_group_ls.insert(0,popped_chrm)
        gamete_lis.append(monosome_lis*2)
        monosome_lis = []
    random.shuffle(gamete_lis)
    return (gamete_lis)


def tetrasomic_split_listing(chr_group):
    monosome_lis = []
    gamete_lis = []
    chr_group_ls = [chr_group[i:i+2] for i in range(0, len(chr_group), 2)]
    for i in range(len(chr_group_ls)):
        popped_chrm = chr_group_ls.pop(-1)
        monosome_lis.append(popped_chrm)
        monosome_lis.append(''.join(chr_group_ls))
        chr_group_ls.insert(0,popped_chrm)
        gamete_lis.append(monosome_lis*2)
        monosome_lis = []
    random.shuffle(gamete_lis)
    return (gamete_lis[:])


def pentasomic_split_listing(chr_group):
    gamete_lis = []
    three_two_ls = []
    one_four_ls = []
    chr_group_ls = [chr_group[i:i+2] for i in range(0, len(chr_group), 2)]
    for i in range(len(chr_group_ls)):
        popped_chrm = chr_group_ls.pop(-1)
        one_four_ls.append(popped_chrm)
        one_four_ls.append(''.join(chr_group_ls))
        chr_group_ls.insert(0,popped_chrm)
        gamete_lis.append(one_four_ls*2)
        one_four_ls = []
    for i in range(len(chr_group_ls)):
        popped_chrm = chr_group_ls.pop(-1)
        popped_chrm = popped_chrm+(chr_group_ls.pop(-1))
        popped_chrm = popped_chrm+(chr_group_ls.pop(-1))
        three_two_ls.append(popped_chrm)
        three_two_ls.append(''.join(chr_group_ls))
        chr_group_ls.insert(0,popped_chrm[0:2])
        chr_group_ls.insert(0,popped_chrm[2:4])
        chr_group_ls.insert(0,popped_chrm[4:6])
        gamete_lis.append(three_two_ls*2)
        three_two_ls = []
    random.shuffle(gamete_lis)
    return (gamete_lis)


def homeolog_ratio_and_weighting_and_total(chr_group):
    """ Extract pairing fidelity values encoded on each chromosome to obtain a mean for the individual.
    :param chr_group holds a single chromosome group, e.g. 'A8A8a8a8'
    :type chr_group: str
    """
    proportion_disomic=99
    if len(chr_group) == 8:
        mei_cost = int(chr_group[1]) + int(chr_group[3]) + int(chr_group[5]) + int(chr_group[7])
        proportion_disomic = round(mei_cost / 4)
    if len(chr_group) == 6:
        mei_cost = int(chr_group[1]) + int(chr_group[3]) + int(chr_group[5])
        proportion_disomic = round(mei_cost / 3)
    if len(chr_group) == 10:
        mei_cost = int(chr_group[1]) + int(chr_group[3]) + int(chr_group[5]) + int(chr_group[7]) + int(chr_group[9])
        proportion_disomic = round(mei_cost / 5)
    tetrasomic_count = 10 - proportion_disomic
    disomic_count = proportion_disomic
    if proportion_disomic == 0:
        disomic_count = 10
        tetrasomic_count = 0
    total_count = (int(len(chr_group)/2))
    return disomic_count, tetrasomic_count, total_count


def dip_list(possible_haploid_chr_complements):
    """ Generate progeny in two steps:
     (1) random selection of haploid chromosome complements for each chromosome group to make gametes.
     (2) random fusion of gametes to produce embryos (endosperm is ignored).
    :arg possible_haploid_chr_complements e.g. [['A8a8','A8A8'....]['B8b8','b8b8'] etc...]
    :type possible_haploid_chr_complements: list of lists
    """
    megagameto = []
    for i in range(240):  # generate 240 megaspores
        gametes = '_'.join([random.choice(l) for l in possible_haploid_chr_complements])
        megagameto.append(gametes)
    microgameto = []
    for i in range(6000):  # generate 6000 microspores
        gametes = '_'.join([random.choice(l) for l in possible_haploid_chr_complements])
        microgameto.append(gametes)
    random.shuffle(microgameto)
    microgameto = microgametophyte_fitness(microgameto)
    random.shuffle(megagameto)
    progeny_list = fuse_gametes(megagameto, microgameto)
    random.shuffle(progeny_list)
    return progeny_list


def fuse_gametes(megagameto, microgameto):
    """ Join haploid phase chromosome complements to make a list of diploid phase chromosome complements.
    Returned karyotypes are formatted as a list of individuals each containing a list of chromosome groups.
    :arg megagameto holds haploid megaspore chromosome combinations, e.g., 'A8a8B8b8C8c8D8d8E8e8F8f8'
    :type megagameto: list
    :arg megagameto holds haploid microspore chromosome combinations, e.g., 'A8a8B8b8C8c8D8d8E8e8F8f8'
    :type microgameto: list
    """
    progeny_list = []
    for n in range(len(megagameto)):
        list_of_doubles = []
        ls_micro = microgameto[n].split('_')
        ls_mega = megagameto[n].split('_')
        for i in range(0,6):
            paired_gametes =ls_micro[i]+ls_mega[i]
            list_of_doubles.append(paired_gametes)
        progeny_list.append(list_of_doubles)
    return progeny_list


def reorder_balanced_2plus2(chr_group):
    """ Reorder gamete combination for homeologues in a 2:2 ratio, for predictable disomic segregation
    e.g., B8b8B8b8 would be returned as B8B8b8b8, i.e. with homologues paired together
    :arg chr_group holds a single chromosome group, of the form 'B8b8B8b8'
    :type chr_group: str
    """
    reordered_chrs = separate_chrom_str(chr_group)
    return ''.join(sorted(reordered_chrs, key=lambda x: x[0]))


def separate_chrom_str(chr_group):
    separated = []
    for i in range(0, len(chr_group), 2):
        separated.append(chr_group[i:i+2])
    return separated


def microgametophyte_fitness(gametophyte_lis):
    """ Generate fitness cost per microgametophyte - based on sum of chromosomal imbalances per group.
    Profiling Note: This is 40% of the run time
    :rtype: list
    """
    costed_gametos = []
    new_list = []
    for gameto in gametophyte_lis:
        diffAa = (((((gameto).count('A') + 1) - ((gameto).count('a') + 1)) ** 2) +
                  ((abs((gameto.count('A') + gameto.count('a')) - 2))*16))  # 0, 4, 16
        diffBb = (((((gameto).count('B') + 1) - ((gameto).count('b') + 1)) ** 2) +
                  ((abs((gameto.count('B') + gameto.count('b')) - 2))*16))  # 0, 4, 16
        diffCc = (((((gameto).count('C') + 1) - ((gameto).count('c') + 1)) ** 2) +
                  ((abs((gameto.count('C') + gameto.count('c')) - 2))*16))  # 0, 4, 16
        diffDd = (((((gameto).count('D') + 1) - ((gameto).count('d') + 1)) ** 2) +
                  ((abs((gameto.count('D') + gameto.count('d')) - 2))*16))  # 0, 4, 16
        diffEe = (((((gameto).count('E') + 1) - ((gameto).count('e') + 1)) ** 2) +
                  ((abs((gameto.count('E') + gameto.count('e')) - 2))*16))  # 0, 4, 16
        diffFf = (((((gameto).count('F') + 1) - ((gameto).count('f') + 1)) ** 2) +
                  ((abs((gameto.count('F') + gameto.count('f')) - 2))*16))  # 0, 4, 16
        total_diffs = diffAa + diffBb + diffCc + diffDd + diffEe + diffFf
        costed_gametos.append((gameto, total_diffs))
    costed_gametos = sorted(costed_gametos, key=itemgetter(1)) # rank by stochiometric imbalance
    for gam in costed_gametos:
        new_list.append(gam[0]) #strip off costing and append to list
    return new_list


def sporophyte_fitness(progeny_list):
    """ Generate fitness cost of each karyotype in a set of progeny - sum of imbalance costs per chromosome group.
    :arg progeny_list holds a list of karyotypes from one parent
    :type progeny_list: list[karyotype lists]
    """
    costed_progeny = []
    random.shuffle(progeny_list)
    for progeny in progeny_list:
        diffAa = (((((progeny[0]).count('A') + 1) - ((progeny[0]).count('a') + 1)) ** 2) +
                  ((abs((progeny[0].count('A') + progeny[0].count('a')) - 4))*16))  # 0, 4, 16
        diffBb = (((((progeny[1]).count('B') + 1) - ((progeny[1]).count('b') + 1)) ** 2) +
                  ((abs((progeny[1].count('B') + progeny[1].count('b')) - 4))*16))  # 0, 4, 16
        diffCc = (((((progeny[2]).count('C') + 1) - ((progeny[2]).count('c') + 1)) ** 2) +
                  ((abs((progeny[2].count('C') + progeny[2].count('c')) - 4))*16))  # 0, 4, 16
        diffDd = (((((progeny[3]).count('D') + 1) - ((progeny[3]).count('d') + 1)) ** 2) +
                  ((abs((progeny[3].count('D') + progeny[3].count('d')) - 4))*16))  # 0, 4, 16
        diffEe = (((((progeny[4]).count('E') + 1) - ((progeny[4]).count('e') + 1)) ** 2) +
                  ((abs((progeny[4].count('E') + progeny[4].count('e')) - 4))*16))  # 0, 4, 16
        diffFf = (((((progeny[5]).count('F') + 1) - ((progeny[5]).count('f') + 1)) ** 2) +
                  ((abs((progeny[5].count('F') + progeny[5].count('f')) - 4))*16))  # 0, 4, 16
        total_diffs = diffAa + diffBb + diffCc + diffDd + diffEe + diffFf
        costed_progeny.append((progeny, total_diffs))
    return costed_progeny


def seed_viability_cut_off(all_progeny):
    """ Generate fitness cost at early phase of sporophyte to filter-out seeds that do not meet minimum fitness score.
    :arg all_progeny holds a list of progeny karyotypes
    :type all_progeny: list of lists
    """
    surviving_progeny = []
    costed_progeny = sporophyte_fitness(all_progeny)  # 0,4,8,16,20,24,32,36,48
    for prog in costed_progeny:
        if prog[1] <= args.seed_viability_cutoff:
            surviving_progeny.append(prog[0])
    return surviving_progeny


def ranked_survival_to_flowering(population_list):
    """ Determine which plants become established based on relative fitness.
    :arg population_list holds all the progeny karyotypes that will be exposed to selection based on relative fitness
    :type population_list: list of lists
    """
    costed_progeny = sporophyte_fitness(population_list)
    costed_progeny = sorted(costed_progeny, key=itemgetter(1))  # 0,4,8,16,20,24,32,36,48, etc...
    i = round(len(costed_progeny) * args.ranked_survival_to_flowering_cutoff)  # 0.5, 0.3, 0.1, etc...
    if i < 1:
        i = 1
    short_list = costed_progeny[0:i]
    successful_progeny = []
    for prog in short_list:
        successful_progeny.append(prog[0])
    return successful_progeny


def determine_current_population_carrying_capacity(pop_size):
    """ Update carrying capacity of population.
    :arg pop_size holds carrying capacity of population
    :type pop_size: int
    """
    if pop_size == 0:  # pop_size of 0 set at beginning of simulation generation 0
        pop_size = int(args.sibling_survival_cutoff / 4) # 25% of viable seeds will reach reproductive stage in genera. 1
    else:
        pop_size = 2 * pop_size  # double pop size for second generation onwards
    if pop_size > args.max_pop_size:
        pop_size = args.max_pop_size
    return pop_size


def apply_selection_to_seeds(progeny_listing):
    """ Determine seed viability and apply chance seed set.
    :arg progeny_listing contains seed karyotypes from each reproducing plant in the given generation
    :type progeny_listing: population list of parent lists of progeny lists
    """
    viable_progeny_listing = []
    for progeny in progeny_listing:
        progeny = seed_viability_cut_off(progeny)  # purge low fitness seeds
        viable_progeny_listing.append(progeny) # no constraints on number of progeny per parent
    return viable_progeny_listing


def do_reports(args, generation_history):
    """ Print reports to files based on what is requested in the command-line arguments.
    :param args passes all command line arguments
    :type args: command-line argument
    :param generation_history
    :type generation_history: List[GenerationState]
    """
    if args.print_eupl_aneu_counts:

        def append_B_U_N_counts_to_lis(karyotype, B_lis, U_lis, N_lis, n_lis):
            B_lis.append(karyotype.count('B'))
            U_lis.append(karyotype.count('U'))
            N_lis.append(karyotype.count('N'))
            n_lis.append(karyotype.count('n'))


        def my_mean(integer_list):
            """ Calculates mean to 2 d.p. or returns 'NA' in case of missing data errors.
            :arg integer_list holds list of counts
            :type integer_list: list
            """
            try:
                mean_val = statistics.mean(integer_list)
                return round(mean_val, 2)
            except (ValueError, TypeError):
                return 'NA'


        report_filename = args.out_name.rstrip()
        print("writing ouput to:", report_filename, "at", datetime.datetime.now().strftime("%H:%M %d/%m/%y"))
        with open(report_filename, 'w') as out_file:
            for n, current_generation in enumerate(generation_history):  # GenerationState
                # B, BU, BUN, BUNn counts
                all_euploid_count = 0
                all_B_U_aneuploid_count = 0
                all_B_U_N_aneuploid_count = 0
                all_B_U_N_n_aneuploid_count = 0
                flowering_euploid_count = 0
                flowering_B_U_aneuploid_count = 0
                flowering_B_U_N_aneuploid_count = 0
                flowering_B_U_N_n_aneuploid_count = 0
                # breakdown for BU individuals from all pool:
                balanced_all_B_and_U = []
                unbalanced_all_B_and_U = []
                nulli_all_B_and_U = []
                num_all_B_and_U = []
                # breakdown for BUN individuals from all pool:
                balanced_all_B_and_U_and_N = []
                unbalanced_all_B_and_U_and_N = []
                nulli_all_B_and_U_and_N = []
                num_all_B_and_U_and_N = []
                # breakdown for BUNn individuals from all pool:
                balanced_all_B_and_U_and_N_and_n = []
                unbalanced_all_B_and_U_and_N_and_n = []
                nulli_all_B_and_U_and_N_and_n = []
                num_all_B_and_U_and_N_and_n = []
                # breakdown for BU individuals from flowering pool:
                balanced_flowering_B_and_U = []
                unbalanced_flowering_B_and_U = []
                nulli_flowering_B_and_U = []
                num_flowering_B_and_U = []
                # breakdown for BUN individuals from flowering pool:
                balanced_flowering_B_and_U_and_N = []
                unbalanced_flowering_B_and_U_and_N = []
                nulli_flowering_B_and_U_and_N = []
                num_flowering_B_and_U_and_N = []
                # breakdown for BUNn individuals from flowering pool:
                balanced_flowering_B_and_U_and_N_and_n = []
                unbalanced_flowering_B_and_U_and_N_and_n = []
                nulli_flowering_B_and_U_and_N_and_n = []
                num_flowering_B_and_U_and_N_and_n = []

                for entry in current_generation.codes_for_viable_seeds:
                    if all(i in entry for i in ['B', 'U', 'N', 'n']) or \
                            all(i in entry for i in ['B', 'N', 'n']) or \
                            all(i in entry for i in ['N', 'n']) or \
                            all(i in entry for i in ['n']):
                        all_B_U_N_n_aneuploid_count +=1
                        append_B_U_N_counts_to_lis(entry, balanced_all_B_and_U_and_N_and_n,
                                                   unbalanced_all_B_and_U_and_N_and_n,
                                                   nulli_all_B_and_U_and_N_and_n,
                                                   num_all_B_and_U_and_N_and_n)
                    else:
                        if all(i in entry for i in ['B', 'U', 'N']) or \
                                all(i in entry for i in ['B', 'N']) or \
                                all(i in entry for i in ['N']):
                            all_B_U_N_aneuploid_count +=1
                            append_B_U_N_counts_to_lis(entry, balanced_all_B_and_U_and_N,
                                                       unbalanced_all_B_and_U_and_N,
                                                       nulli_all_B_and_U_and_N,
                                                       num_all_B_and_U_and_N)
                        else:
                            if all(i in entry for i in ['B', 'U']) or \
                                    all(i in entry for i in ['U']):
                                all_B_U_aneuploid_count +=1
                                append_B_U_N_counts_to_lis(entry, balanced_all_B_and_U,
                                                           unbalanced_all_B_and_U,
                                                           nulli_all_B_and_U,
                                                           num_all_B_and_U)
                            else:
                                if all(i in entry for i in ['B']):
                                    all_euploid_count +=1
                for entry in current_generation.codes_for_reproducing_individuals:
                    if all(i in entry for i in ['B', 'U', 'N', 'n']) or \
                            all(i in entry for i in ['B', 'N', 'n']) or \
                            all(i in entry for i in ['N', 'n']) or \
                            all(i in entry for i in ['n']):
                        flowering_B_U_N_n_aneuploid_count +=1
                        append_B_U_N_counts_to_lis(entry, balanced_flowering_B_and_U_and_N_and_n,
                                                   unbalanced_flowering_B_and_U_and_N_and_n,
                                                   nulli_flowering_B_and_U_and_N_and_n,
                                                   num_flowering_B_and_U_and_N_and_n)
                    else:
                        if all(i in entry for i in ['B', 'U', 'N']) or \
                                all(i in entry for i in ['B', 'N']) or \
                                all(i in entry for i in ['N']):
                            flowering_B_U_N_aneuploid_count +=1
                            append_B_U_N_counts_to_lis(entry, balanced_flowering_B_and_U_and_N,
                                                       unbalanced_flowering_B_and_U_and_N,
                                                       nulli_flowering_B_and_U_and_N,
                                                       num_flowering_B_and_U_and_N)
                        else:
                            if all(i in entry for i in ['B', 'U']) or \
                                    all(i in entry for i in ['U']):
                                flowering_B_U_aneuploid_count +=1
                                append_B_U_N_counts_to_lis(entry, balanced_flowering_B_and_U,
                                                           unbalanced_flowering_B_and_U,
                                                           nulli_flowering_B_and_U,
                                                           num_flowering_B_and_U)
                            else:
                                if all(i in entry for i in ['B']):
                                    flowering_euploid_count +=1

                order_derived = [n, args.generations, args.max_pop_size, args.seed_viability_cutoff,
                                 args.ranked_survival_to_flowering_cutoff, args.sibling_survival_cutoff,
                                 args.starting_karyotype, args.non_numerical_multiplier,
                                 current_generation.count_of_stable_mature_individuals, all_euploid_count,
                                 all_B_U_aneuploid_count, all_B_U_N_aneuploid_count,all_B_U_N_n_aneuploid_count,
                                 flowering_euploid_count, flowering_B_U_aneuploid_count,flowering_B_U_N_aneuploid_count,
                                 flowering_B_U_N_n_aneuploid_count]
                ordering_variables = [current_generation.tetrasomic_dict[chrom] for chrom in chr_range]
                out_file.write(','.join([str(x) for x in order_derived + ordering_variables]) + ',')
                order_mean_stats = (
                    balanced_all_B_and_U, unbalanced_all_B_and_U, nulli_all_B_and_U,
                    balanced_all_B_and_U_and_N, unbalanced_all_B_and_U_and_N, nulli_all_B_and_U_and_N,
                    balanced_all_B_and_U_and_N_and_n, unbalanced_all_B_and_U_and_N_and_n,
                    nulli_all_B_and_U_and_N_and_n, num_all_B_and_U_and_N_and_n,
                    balanced_flowering_B_and_U, unbalanced_flowering_B_and_U, nulli_flowering_B_and_U,
                    balanced_flowering_B_and_U_and_N, unbalanced_flowering_B_and_U_and_N, nulli_flowering_B_and_U_and_N,
                    balanced_flowering_B_and_U_and_N_and_n, unbalanced_flowering_B_and_U_and_N_and_n,
                    nulli_flowering_B_and_U_and_N_and_n, num_flowering_B_and_U_and_N_and_n)
                out_file.write(','.join([str(my_mean(x)) for x in order_mean_stats]) + '\n')


def str2bool(cmd_value):
    """Parses cmd_value into a boolean variable
    Example from user Maxim:
    https://stackoverflow.com/questions/15008758/parsing-boolean-values-with-argparse"""
    if cmd_value.lower() in ('yes', 'true', 'y'):
        return True
    elif cmd_value.lower() in ('no', 'false', 'n'):
        return False
    else:
        raise argparse.ArgumentTypeError('Use y or n to specify boolean argument.')


if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    # INPUT OPTIONS
    parser.add_argument('--max_pop_size', required=True, type=int, help="Maximum population size")
    parser.add_argument('--generations', required=True, type=int, help="Total number of generations")
    parser.add_argument('--seed_viability_cutoff', required=True, type=int, default=20,
                        help="Maximum imbalance cost for a seed to still be viable")
    parser.add_argument('--sibling_survival_cutoff', required=True, type=int, default=60,
                        help="Maximum number of seeds that can possibly establish out of a maximum 240 seeds per "
                             "parent plant")
    parser.add_argument('--starting_karyotype', required=True, type=str, default=80,
                        help="Set founder karyotype with percentage stringency e.g. 20 or "
                             "karyotypes of the form (PD_xx_yy_a_b) e.g. PD_80_100_99_1 "
                             "where xx is low stringency percentage, yy is high stringency percentage, a is "
                             "number of low stringency of indivs and b is number of high stringency indivs")
    parser.add_argument('--ranked_survival_to_flowering_cutoff', required=True, type=float, default=0.50,
                        help="Fraction of plants in population that will survive to flowering")
    parser.add_argument('--aneuploid_pairing_bias', default=4, type=int,
                        help="Controls skew applied to meiosis involving 1:3 complements, to account for the increased "
                             "transmission of the trisomic chromsome relative to the monosome. Note that a value of "
                             "4 was found to yield biologically realistic results for Tragopogon miscellus.")
    parser.add_argument('--non_numerical_multiplier', default=3, type=int,
                        help="Integer-based weighting to alter the number of non-numerical gametophyte sets "
                             "relative to the number of numerical gaemtophyte sets.")

    # OUTPUT OPTIONS
    parser.add_argument('--print_eupl_aneu_counts', type=str2bool, nargs='?', const=True, default=True,
                        help="Print output counts (Y/n)")
    parser.add_argument("--germinated_karyotypes", type=str2bool, nargs='?', const=True, default=False,
                        help="Print list of all karyotypes that germinated in final generation (y/N).")
    parser.add_argument('--adult_karyotypes', type=str2bool, nargs='?', const=True, default=False,
                        help="Print list of all karyotypes that reached flowering in final generation (y/N).")
    parser.add_argument('--out_name', required=True, type=str, help="Full path and name of output file.")
    parser.add_argument('--test', required=False, action='store_true',
                        help="Use a fixed random number generator seed to always produce the same test output.")
    args = parser.parse_args()

    if args.test:
        random.seed(154897491)  # for deterministic testing, don't use for research.
    simulation = KaryotypeSimulation(args.germinated_karyotypes, args.adult_karyotypes,
                                     args.aneuploid_pairing_bias)
    simulation.run_simulation()
    do_reports(args, simulation.generation_history)

