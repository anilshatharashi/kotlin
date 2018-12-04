/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.resolve.lazy.descriptors.script

import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.descriptors.annotations.Annotations
import org.jetbrains.kotlin.descriptors.impl.PropertyDescriptorImpl
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.resolve.lazy.descriptors.LazyScriptDescriptor
import org.jetbrains.kotlin.types.KotlinType

class ReplResultPropertyDescriptor(
    name: Name,
    kotlinType: KotlinType,
    receiver: ReceiverParameterDescriptor?,
    script: LazyScriptDescriptor,
    source: SourceElement
) : PropertyDescriptorImpl(
    script,
    null,
    Annotations.EMPTY,
    Modality.FINAL,
    Visibilities.PUBLIC,
    false,
    name,
    CallableMemberDescriptor.Kind.SYNTHESIZED,
    source,
    /* lateInit = */ false, /* isConst = */ false, /* isExpect = */ false, /* isActual = */ false, /* isExternal = */ false,
    /* isDelegated = */ false
) {
    init {
        setType(kotlinType, emptyList(), receiver, null)
        initialize(
            null, null
        )
    }
}