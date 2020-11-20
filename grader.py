#!/usr/bin/env python3

from logic import *

import pickle, gzip, os, random
import graderUtil

grader = graderUtil.Grader()
submission = grader.load('submission')

# name: name of this formula (used to load the models)
# predForm: the formula predicted in the submission
# preconditionForm: only consider models such that preconditionForm is true
def checkFormula(name, predForm, preconditionForm=None):
    filename = os.path.join('models', name + '.pklz')
    objects, targetModels = pickle.load(gzip.open(filename))
    # If preconditionion exists, change the formula to
    preconditionPredForm = And(preconditionForm, predForm) if preconditionForm else predForm
    predModels = performModelChecking([preconditionPredForm], findAll=True, objects=objects)
    ok = True
    def hashkey(model): return tuple(sorted(str(atom) for atom in model))
    targetModelSet = set(hashkey(model) for model in targetModels)
    predModelSet = set(hashkey(model) for model in predModels)
    for model in targetModels:
        if hashkey(model) not in predModelSet:
            grader.fail("Your formula (%s) says the following model is FALSE, but it should be TRUE:" % predForm)
            ok = False
            printModel(model)
            return
    for model in predModels:
        if hashkey(model) not in targetModelSet:
            grader.fail("Your formula (%s) says the following model is TRUE, but it should be FALSE:" % predForm)
            ok = False
            printModel(model)
            return
    grader.add_message('You matched the %d models' % len(targetModels))
    grader.add_message('Example model: %s' % rstr(random.choice(targetModels)))
    grader.assign_full_credit()

# name: name of this formula set (used to load the models)
# predForms: formulas predicted in the submission
# predQuery: query formula predicted in the submission
def addParts(name, numForms, predictionFunc):
    # part is either an individual formula (0:numForms), all (combine everything)
    def check(part):
        predForms, predQuery = predictionFunc()
        if len(predForms) < numForms:
            grader.fail("Wanted %d formulas, but got %d formulas:" % (numForms, len(predForms)))
            for form in predForms: print(('-', form))
            return
        if part == 'all':
            checkFormula(name + '-all', AndList(predForms))
        elif part == 'run':
            # Actually run it on a knowledge base
            #kb = createResolutionKB()  # Too slow!
            kb = createModelCheckingKB()

            # Need to tell the KB about the objects to do model checking
            filename = os.path.join('models', name + '-all.pklz')
            objects, targetModels = pickle.load(gzip.open(filename))
            for obj in objects:
                kb.tell(Atom('Object', obj))

            # Add the formulas
            for predForm in predForms:
                response = kb.tell(predForm)
                showKBResponse(response)
                grader.require_is_equal(CONTINGENT, response.status)
            response = kb.ask(predQuery)
            showKBResponse(response)

        else:  # Check the part-th formula
            checkFormula(name + '-' + str(part), predForms[part])

    def createCheck(part): return lambda : check(part)  # To create closure

    for part in list(range(numForms)) + ['all', 'run']:
        if part == 'all':
            description = 'test implementation of %s for %s' % (part, name)
        elif part == 'run':
            description = 'test implementation of %s for %s' % (part, name)
        else:
            description = 'test implementation of statement %s for %s' % (part, name)
        grader.add_basic_part(name + '-' + str(part), createCheck(part), max_points=1, max_seconds=10000, description=description)

############################################################
# Problem 1: propositional logic

grader.add_basic_part('1a', lambda : checkFormula('1a', submission.formula1a()), 2, description='Test formula 1a implementation')
grader.add_basic_part('1b', lambda : checkFormula('1b', submission.formula1b()), 2, description='Test formula 1b implementation')
grader.add_basic_part('1c', lambda : checkFormula('1c', submission.formula1c()), 2, description='Test formula 1c implementation')

############################################################
# Problem 2: first-order logic

formula2a_precondition = AntiReflexive('Mother')
formula2b_precondition = AntiReflexive('Child')
formula2c_precondition = AntiReflexive('Child')
formula2d_precondition = AntiReflexive('Parent')
grader.add_basic_part('2a', lambda : checkFormula('2a', submission.formula2a(), formula2a_precondition), 2, description='Test formula 2a implementation')
grader.add_basic_part('2b', lambda : checkFormula('2b', submission.formula2b(), formula2b_precondition), 2, description='Test formula 2b implementation')
grader.add_basic_part('2c', lambda : checkFormula('2c', submission.formula2c(), formula2c_precondition), 2, description='Test formula 2c implementation')
grader.add_basic_part('2d', lambda : checkFormula('2d', submission.formula2d(), formula2d_precondition), 2, description='Test formula 2d implementation')

############################################################
# Problem 3: liar puzzle

# Add 3a-[0-5], 3a-all, 3a-run
addParts('3a', 6, submission.liar)

############################################################
# Problem 4: Modus Ponens

grader.add_manual_part('4a', 5, description='Test CNF conversion and new Modus ponens rule to derive C')
grader.add_manual_part('4b', 5, description='Test usage of the resolution rule to derive D')

############################################################
# Problem 5: odd and even integers

# Add 5a-[0-5], 5a-all, 5a-run
addParts('5a', 6, submission.ints)

############################################################
# Problem 6: semantic parsing

import nlparser

def getTopDerivation(sentence, languageProcessor, grammar):
    # Return (action, formula)
    # - action is either |tell| or |ask|
    # - formula is a logical form
    print()
    print(('>>>', sentence))
    utterance = nlparser.Utterance(sentence, languageProcessor)
    print(('Utterance:', utterance))
    derivations = nlparser.parseUtterance(utterance, grammar, verbose=0)
    if not derivations:
        raise Exception('Error: Parsing failed. (0 derivations)')
    return derivations[0].form

def testKnowledgeBase(examples, ruleCreator):
    # Test the logical forms by querying the knowledge base.
    kb = createModelCheckingKB()
    #kb = createResolutionKB()
    languageProcessor = nlparser.createBaseLanguageProcessor()
    # Need to tell kb about objects
    for obj in nlparser.BASE_OBJECTS:
        kb.tell(Atom('Object', obj.lower()))

    # Parse!
    grammar = nlparser.createBaseEnglishGrammar() + [ruleCreator()]
    for sentence, expectedResult in examples:
        mode, formula = getTopDerivation(sentence, languageProcessor, grammar)
        print(('The parser returns:', (mode, formula)))
        grader.require_is_equal(expectedResult[0], mode)
        if mode == 'tell':  response = kb.tell(formula)
        if mode == 'ask':   response = kb.ask(formula)
        print(('Knowledge base returns:', response))
        grader.require_is_equal(expectedResult[1], response.status)
        #kb.dump()

### 6a

def test_6a_1():
    examples = [
        ('Every person likes some cat.', ('tell', CONTINGENT)),
        ('Every cat is a mammal.', ('tell', CONTINGENT)),
        ('Every person likes some mammal?', ('ask', ENTAILMENT)),
    ]
    testKnowledgeBase(examples, submission.createRule1)
grader.add_basic_part('6a-1', test_6a_1, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6a_2():
    examples = [
        ('Every person likes some cat.', ('tell', CONTINGENT)),
        ('Every tabby is a cat.', ('tell', CONTINGENT)),
        ('Every person likes some tabby?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule1)
grader.add_basic_part('6a-2', test_6a_2, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6a_3():
    examples = [
        ('Every person likes some cat.', ('tell', CONTINGENT)),
        ('Every person is a mammal.', ('tell', CONTINGENT)),
        ('Every mammal likes some cat?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule1)
grader.add_basic_part('6a-3', test_6a_3, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6a_4():
    examples = [
        ('Every person likes some cat.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule1)
grader.add_basic_part('6a-4', test_6a_4, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6a_5():
    examples = [
        ('Every person likes some cat.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule1)
grader.add_basic_part('6a-5', test_6a_5, max_points=1, max_seconds=60, description='Check basic behavior of rule')

### 6b

def test_6b_1():
    examples = [
        ('There is some cat that every person likes.', ('tell', CONTINGENT)),
        ('Every cat is a mammal.', ('tell', CONTINGENT)),
        ('There is some mammal that every person likes?', ('ask', ENTAILMENT)),
    ]
    testKnowledgeBase(examples, submission.createRule2)
grader.add_basic_part('6b-1', test_6b_1, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6b_2():
    examples = [
        ('There is some cat that every person likes.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes some cat?', ('ask', ENTAILMENT)),
    ]
    testKnowledgeBase(examples, submission.createRule2)
grader.add_basic_part('6b-2', test_6b_2, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6b_3():
    examples = [
        ('There is some cat that every person likes.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule2)
grader.add_basic_part('6b-3', test_6b_3, max_points=1, max_seconds=60, description='Check basic behavior of rule')

### 6c

def test_6c_1():
    examples = [
        ('If a person likes a cat then the former feeds the latter.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes Garfield.', ('tell', CONTINGENT)),
        ('Jon feeds Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule3)
grader.add_basic_part('6c-1', test_6c_1, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6c_2():
    examples = [
        ('If a person likes a cat then the former feeds the latter.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes Garfield.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon feeds Garfield?', ('ask', ENTAILMENT)),
    ]
    testKnowledgeBase(examples, submission.createRule3)
grader.add_basic_part('6c-2', test_6c_2, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6c_3():
    examples = [
        ('If a person likes a cat then the former feeds the latter.', ('tell', CONTINGENT)),
        ('Jon likes Garfield.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon feeds Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule3)
grader.add_basic_part('6c-3', test_6c_3, max_points=1, max_seconds=60, description='Check basic behavior of rule')

def test_6c_4():
    examples = [
        ('If a person likes a cat then the former feeds the latter.', ('tell', CONTINGENT)),
        ('Jon is a person.', ('tell', CONTINGENT)),
        ('Jon likes some cat.', ('tell', CONTINGENT)),
        ('Garfield is a cat.', ('tell', CONTINGENT)),
        ('Jon feeds Garfield?', ('ask', CONTINGENT)),
    ]
    testKnowledgeBase(examples, submission.createRule3)
grader.add_basic_part('6c-4', test_6c_4, max_points=1, max_seconds=60, description='Check basic behavior of rule')

grader.grade()
