/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.contracts.contextual.safebuilders.serialization

import org.jetbrains.kotlin.contracts.ContractDeserializerImpl
import org.jetbrains.kotlin.contracts.contextual.model.CleanerDeclaration
import org.jetbrains.kotlin.contracts.contextual.model.ProviderDeclaration
import org.jetbrains.kotlin.contracts.contextual.model.VerifierDeclaration
import org.jetbrains.kotlin.contracts.contextual.safebuilders.CallCleanerDeclaration
import org.jetbrains.kotlin.contracts.contextual.safebuilders.CallProviderDeclaration
import org.jetbrains.kotlin.contracts.contextual.safebuilders.CallVerifierDeclaration
import org.jetbrains.kotlin.contracts.contextual.serialization.SubpluginContractDeserializer
import org.jetbrains.kotlin.contracts.contextual.serialization.getExtendedProto
import org.jetbrains.kotlin.contracts.description.expressions.ContractDescriptionValue
import org.jetbrains.kotlin.metadata.extension.contracts.ContractsProtoBuf
import org.jetbrains.kotlin.metadata.extension.contracts.subplugin.ContractSubpluginsProtoBuf

class CallContractDeserializer : SubpluginContractDeserializer {
    override fun deserializeContextProvider(
        proto: ContractsProtoBuf.ContextProvider,
        worker: ContractDeserializerImpl.ContractDeserializationWorker,
        references: List<ContractDescriptionValue>
    ): ProviderDeclaration? = CallProviderDeclaration(references)

    override fun deserializeContextVerifier(
        proto: ContractsProtoBuf.ContextVerifier,
        worker: ContractDeserializerImpl.ContractDeserializationWorker,
        references: List<ContractDescriptionValue>
    ): VerifierDeclaration? {
        val extendedProto = getExtendedProto(proto)
        if (!extendedProto.hasExtension(ContractSubpluginsProtoBuf.verifierCallKind)) return null
        val kind = worker.extractInvocationKind(extendedProto.getExtension(ContractSubpluginsProtoBuf.verifierCallKind)) ?: return null
        return CallVerifierDeclaration(kind, references)
    }

    override fun deserializeContextCleaner(
        proto: ContractsProtoBuf.ContextCleaner,
        worker: ContractDeserializerImpl.ContractDeserializationWorker,
        references: List<ContractDescriptionValue>
    ): CleanerDeclaration? {
        val extendedProto = getExtendedProto(proto)
        if (!extendedProto.hasExtension(ContractSubpluginsProtoBuf.cleanerCallKind)) return null
        val kind = worker.extractInvocationKind(extendedProto.getExtension(ContractSubpluginsProtoBuf.cleanerCallKind)) ?: return null
        return CallCleanerDeclaration(kind, references)
    }
}