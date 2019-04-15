/*
 * Copyright 2010-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.resolve.calls

import org.jetbrains.kotlin.fir.declarations.FirFunction
import org.jetbrains.kotlin.fir.resolve.transformers.firUnsafe
import org.jetbrains.kotlin.fir.symbols.impl.FirCallableSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirFunctionSymbol
import org.jetbrains.kotlin.fir.types.ConeKotlinType
import org.jetbrains.kotlin.fir.types.FirResolvedTypeRef
import org.jetbrains.kotlin.resolve.calls.tasks.ExplicitReceiverKind
import org.jetbrains.kotlin.resolve.calls.tasks.ExplicitReceiverKind.*
import java.lang.IllegalStateException


abstract class ResolutionStage {
    abstract fun check(candidate: Candidate, sink: CheckerSink, callInfo: CallInfo)
}

abstract class CheckerStage : ResolutionStage()

internal object CheckExplicitReceiverConsistency : ResolutionStage() {
    override fun check(candidate: Candidate, sink: CheckerSink, callInfo: CallInfo) {
        val receiverKind = candidate.explicitReceiverKind
        val explicitReceiver = callInfo.explicitReceiver
        // TODO: add invoke cases
        when (receiverKind) {
            NO_EXPLICIT_RECEIVER -> {
                if (explicitReceiver != null) return sink.reportApplicability(CandidateApplicability.WRONG_RECEIVER)
            }
            EXTENSION_RECEIVER, DISPATCH_RECEIVER -> {
                if (explicitReceiver == null) return sink.reportApplicability(CandidateApplicability.WRONG_RECEIVER)
            }
            BOTH_RECEIVERS -> {
                if (explicitReceiver == null) return sink.reportApplicability(CandidateApplicability.WRONG_RECEIVER)
                // Here we should also check additional invoke receiver
            }
        }
    }

}

internal sealed class CheckReceivers : ResolutionStage() {
    object Dispatch : CheckReceivers() {
        override fun ExplicitReceiverKind.shouldBeResolvedAsImplicit(): Boolean {
            return this == EXTENSION_RECEIVER || this == NO_EXPLICIT_RECEIVER
        }

        override fun ExplicitReceiverKind.shouldBeResolvedAsExplicit(): Boolean {
            return this == DISPATCH_RECEIVER || this == BOTH_RECEIVERS
        }

        override fun Candidate.getReceiverValue(): ReceiverValue? {
            return dispatchReceiverValue
        }
    }

    object Extension : CheckReceivers() {
        override fun ExplicitReceiverKind.shouldBeResolvedAsImplicit(): Boolean {
            return this == DISPATCH_RECEIVER || this == NO_EXPLICIT_RECEIVER
        }

        override fun ExplicitReceiverKind.shouldBeResolvedAsExplicit(): Boolean {
            return this == EXTENSION_RECEIVER || this == BOTH_RECEIVERS
        }

        override fun Candidate.getReceiverValue(): ReceiverValue? {
            val callableSymbol = symbol as? FirCallableSymbol ?: return null
            val callable = callableSymbol.fir
            val type = (callable.receiverTypeRef as FirResolvedTypeRef?)?.type ?: return null
            return object : ReceiverValue {
                override val type: ConeKotlinType
                    get() = type

            }
        }
    }

    abstract fun Candidate.getReceiverValue(): ReceiverValue?

    abstract fun ExplicitReceiverKind.shouldBeResolvedAsExplicit(): Boolean

    abstract fun ExplicitReceiverKind.shouldBeResolvedAsImplicit(): Boolean

    private fun List<ImplicitReceiverValue>.findMatchingImplicitReceiverValue(
        receiverParameterValue: ReceiverValue
    ): ImplicitReceiverValue? {
        if (receiverParameterValue is ClassDispatchReceiverValue) {
            val candidateClassSymbol = receiverParameterValue.klassSymbol
            var takeDispatchReceivers = true
            for (implicitReceiverValue in this) {
                if (implicitReceiverValue is ImplicitDispatchReceiverValue) {
                    if (!takeDispatchReceivers) continue
                    val implicitReceiverBoundClassSymbol = implicitReceiverValue.boundSymbol
                    if (!implicitReceiverBoundClassSymbol.fir.isInner) {
                        takeDispatchReceivers = false
                    }
                    if (implicitReceiverBoundClassSymbol == candidateClassSymbol) {
                        return implicitReceiverValue
                    }
                }
            }
        }
        // TODO: temporary
        return firstOrNull()
    }

    override fun check(candidate: Candidate, sink: CheckerSink, callInfo: CallInfo) {
        val receiverParameterValue = candidate.getReceiverValue()
        val explicitReceiverExpression = callInfo.explicitReceiver
        val explicitReceiverKind = candidate.explicitReceiverKind

        if (receiverParameterValue != null) {
            if (explicitReceiverExpression != null && explicitReceiverKind.shouldBeResolvedAsExplicit()) {
                resolveArgumentExpression(
                    candidate.csBuilder, explicitReceiverExpression, receiverParameterValue.type,
                    sink, isReceiver = true, typeProvider = callInfo.typeProvider
                )
            } else if (explicitReceiverExpression == null && explicitReceiverKind.shouldBeResolvedAsImplicit()) {
                val implicitReceiverValues = callInfo.implicitReceiverValues

                // TODO: this is very preliminary. We should take receiver value matching this candidate, not just the first one
                val implicitReceiverValue = implicitReceiverValues.findMatchingImplicitReceiverValue(receiverParameterValue)
                    ?: return sink.reportApplicability(CandidateApplicability.WRONG_RECEIVER)
                resolvePlainArgumentType(
                    candidate.csBuilder, implicitReceiverValue.type, receiverParameterValue.type, sink, isReceiver = true
                )
            }
        }
    }
}

internal object MapArguments : ResolutionStage() {
    override fun check(candidate: Candidate, sink: CheckerSink, callInfo: CallInfo) {
        val symbol = candidate.symbol as? FirFunctionSymbol ?: return sink.reportApplicability(CandidateApplicability.HIDDEN)
        val function = symbol.firUnsafe<FirFunction>()
        val processor = FirCallArgumentsProcessor(function, callInfo.arguments)
        val mappingResult = processor.process()
        candidate.argumentMapping = mappingResult.argumentMapping
        if (!mappingResult.isSuccess) {
            return sink.reportApplicability(CandidateApplicability.PARAMETER_MAPPING_ERROR)
        }
    }

}

internal object CheckArguments : CheckerStage() {
    override fun check(candidate: Candidate, sink: CheckerSink, callInfo: CallInfo) {
        val argumentMapping =
            candidate.argumentMapping ?: throw IllegalStateException("Argument should be already mapped while checking arguments!")
        for ((argument, parameter) in argumentMapping) {
            candidate.resolveArgument(argument, parameter, isReceiver = false, typeProvider = callInfo.typeProvider, sink = sink)
        }

        if (candidate.system.hasContradiction) {
            sink.reportApplicability(CandidateApplicability.INAPPLICABLE)
        }
    }

}


internal fun functionCallResolutionSequence() = listOf(
    CheckExplicitReceiverConsistency, CheckReceivers.Dispatch, CheckReceivers.Extension,
    MapArguments, CreateFreshTypeVariableSubstitutorStage, CheckArguments
)


internal fun qualifiedAccessResolutionSequence() = listOf(
    CheckExplicitReceiverConsistency, CheckReceivers.Dispatch, CheckReceivers.Extension,
    CreateFreshTypeVariableSubstitutorStage
)